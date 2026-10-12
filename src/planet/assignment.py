from z3 import *
from .helpers import *
from .narray import *
from .candl import *
from .unit import Clusters
import pandas as pd
import math
import random
import warnings
from pathlib import Path
import duckdb
from planet.plans import PlanGenerator
from planet.formatter import LatexExport


def determine_plans(units, design):
    n = len(units)
    plans = PlanGenerator(design, n)
    return plans.generate()


class Assignment:
    def __init__(self, units, plans, strict = False):
        assign_counterbalance(units, plans, strict = strict)
        self.units = units
        self.plans = plans
        self.computed_plans = determine_plans(units, plans)
    
    def format_plans(self):
        matrix = self.computed_plans
        ret = ""

        for i in range(len(matrix)):
            ret += f"plan {i+1}:\n\t" 
            for j in range(len(matrix[i])):

                end = "" if j == len(matrix[i]) - 1 else "\t" 
                conditions = matrix[i][j].split("-")
                test = [f"{self.plans.variables[x].name} = {conditions[x]}" for x in range(len(conditions))]
                conditions = ", ".join(test)

                ret += f"trial {j+1}: {str(conditions)}\n" + end
        return ret
    
   
    def to_csv(self):
        plans = self.computed_plans

        trials = [f"trial{i+1}" for i in range(len(plans[0]))]
        df = pd.DataFrame(plans, columns=trials)
        units_df = self.format_assignment()

        OUTPUT_PATH = Path("outputs") / "assignment.csv"
        OUTPUT_PATH.parent.mkdir(parents=True, exist_ok=True)  # create folder if needed

        df = df.reset_index()
        df = df.rename(columns={'index': 'row_number'})
        df = units_df.merge(df, how='inner', left_on='plan', right_on='row_number')
        df = df.drop("row_number", axis=1)
        df.to_csv(OUTPUT_PATH, index=False)

    def to_latex(self):
        # FIXME: won't work with random plans
        matrix = self.computed_plans
        formatter = LatexExport(matrix)
        formatter.to_latex()
    
    def format_assignment(self):
        return duckdb.sql(f"select * from {self.units.table}").to_df()
        
    def __str__(self):
        ret = f"""***EXPERIMENT PLANS***\n\n{str(self.format_plans())} \n\n***ASSIGNMENT***\n\n{str(self.format_assignment())}"""
        return ret

def assign_subunits(units, parent):
    duckdb.sql(f""" update {units.table}
                        set plan = subunit_assignment.plan
                        from 
                            (
                                select units.pid id, expanded_cluster_assignment.plan plan  
                                from {units.table} units, 
                                    ( select plan, unnest(subunits) test 
                                      from {parent.table} 
                                    ) as expanded_cluster_assignment
                                where units.pid = expanded_cluster_assignment.test
                            ) subunit_assignment

                        where subunit_assignment.id = {units.table}.pid
        
           """)


def allocation_warning(num_units, num_plans, noun="units"):
    """The warning for an assignment that cannot give every plan the same
    number of units, or None when the plans divide the units.

    It says how the units fall on the plans and names the nearest number of
    units that the plans divide. When the next smaller and the next larger
    multiple are equally near, it names the larger.
    """
    def count(k, singular):
        return f"{k} {singular if k == 1 else singular + 's'}"

    one = noun[:-1]
    base, extra = divmod(num_units, num_plans)
    if not extra:
        return None
    if base == 0:
        unused = num_plans - num_units
        return (
            f"Assigning {count(num_units, one)} to {num_plans} plans: "
            f"{count(unused, 'plan')} {'is' if unused == 1 else 'are'} not used, so the "
            f"properties of the design do not hold over these {noun}. "
            f"Use at least {num_plans} {noun}, one for each plan."
        )
    fewer, more = extra, num_plans - extra
    if more <= fewer:
        advice = f"{num_units + more} {noun} ({more} more)"
    else:
        advice = f"{num_units - fewer} {noun} ({fewer} fewer)"
    return (
        f"Assigning {num_units} {noun} to {num_plans} plans: "
        f"{count(extra, 'plan')} {'receives' if extra == 1 else 'receive'} {base + 1} {noun} "
        f"and {count(more, 'plan')} {'receives' if more == 1 else 'receive'} "
        f"{count(base, one)}, so the properties of the design do not hold exactly "
        f"over these {noun}. Use {advice} to give every plan the same number."
    )


def allocate_rows(num_rows, num_plans, num_participants):
    """A row of the plan table for each participant, in random order.

    Every plan receives the same number of participants when the plans divide
    them. Otherwise the counts differ by at most one, and the plans that
    receive one more are chosen at random.

    `num_rows` is `num_plans` for a design without random variables. With
    random variables each plan is expanded to `num_rows / num_plans`
    consecutive rows, one random draw each, and every participant gets a row
    of their own.
    """
    copies = num_rows // num_plans
    base, extra = divmod(num_participants, num_plans)
    one_more = set(random.sample(range(num_plans), extra))
    rows = []
    for plan in range(num_plans):
        for k in range(base + (plan in one_more)):
            rows.append(plan * copies + k if copies > 1 else plan)
    random.shuffle(rows)
    return rows


def construct_assignment_table(table, num_rows, num_plans, num_participants):
    rows = allocate_rows(num_rows, num_plans, num_participants)
    if not rows:
        return
    values = ", ".join(f"({pid}, {row})" for pid, row in enumerate(rows, start=1))
    duckdb.sql(f"""
        UPDATE {table}
        SET plan = assignment.plan
        FROM (VALUES {values}) AS assignment(pid, plan)
        WHERE assignment.pid = {table}.pid
    """)


def assign_units(units, plans, strict=False):
    """
    Assigns every participant (unit) to a plan, as evenly as the numbers allow.

    When the design's number of plans divides the number of units, every plan
    receives the same number of units. Otherwise the assignment still covers
    every unit, the numbers of units per plan differ by at most one, and a
    warning says how they fall and which number of units would make them equal.
    With `strict`, that case raises ValueError with the same message instead,
    before the units' table is created or changed.

    Parameters:
    units : object
        An object containing participant data and metadata.
    plans : object
        An object containing plan assignment logic.
    """
    num_participants = len(units)  # Total number of participants
    generator = PlanGenerator(plans, num_participants)
    rows = generator.generate()
    # The plans of the design. With random variables, `rows` holds one row
    # per unit, each with its own random draw; the plans are still the rows
    # the solver found.
    num_plans = generator.num_plans
    noun = "clusters" if isinstance(units, Clusters) else "units"
    message = allocation_warning(num_participants, num_plans, noun)
    if message and strict:
        raise ValueError(message)
    if message:
        warnings.warn(message, stacklevel=5)

    # Evaluate the units object to ensure it's up-to-date
    table = units.get_table()
    if len(rows):
        construct_assignment_table(table, len(rows), num_plans, num_participants)


def assign_counterbalance(units, plans, parent = None, strict = False):
    if parent is not None:
        assign_subunits(units, parent)
    else:
        assign_units(units, plans, strict)
        
    # NOTE: assign subunits to the same plan as their parent unit was assigned to 
    if isinstance(units, Clusters):
        assign_counterbalance(units.units, plans, parent = units)


def assign(units, plans, strict = False):
    """Assign the units to the plans of the design.

    Every unit gets a plan. If the plans do not divide the units, the plans
    cannot all receive the same number of units: the assignment is then as
    even as possible and a warning says so. With `strict=True` that case
    raises ValueError instead and the units are left unchanged.
    """
    return Assignment(units, plans, strict)


       