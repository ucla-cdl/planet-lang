from z3 import *
from .helpers import *
from .narray import *
from .candl import *
from .unit import Clusters
import pandas as pd
import math
from pathlib import Path
import duckdb
from planet.plans import PlanGenerator
from planet.formatter import LatexExport


def determine_plans(units, design):
    n = len(units)
    plans = PlanGenerator(design, n)
    return plans.generate()


class Assignment:
    def __init__(self, units, plans):
        assign_counterbalance(units, plans)
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


def construct_assignment_table(table, units, num_plans, num_participants):
     # Create a temporary table to store plan assignments
    duckdb.sql("CREATE TABLE members (plan INT)")

   
    required_participants = math.ceil(num_participants/num_plans) * num_plans if num_participants else num_plans

    num_new = required_participants - num_participants
    if num_new > 0:
        duckdb.sql(f"""
            INSERT INTO {units.table}
            SELECT i + {num_participants + 1}, 0 FROM range({num_new}) AS t(i)
        """)
    
    num_per_group = required_participants // num_plans  # Number of participants per plan
    
    # Insert plan assignments into the temporary table
    duckdb.sql(f"""
        INSERT INTO members
        SELECT plan 
        FROM (
            SELECT i AS plan 
            FROM range({num_plans}) AS t(i)
        ) plans
        CROSS JOIN (
            SELECT i AS repeat FROM range({num_per_group}) AS r(i)
        ) repeats
    """ )
    
    # Randomly distribute the plan assignments to the participants
    duckdb.sql(f"""
        UPDATE {table}
        SET plan = assignment.plan
        FROM (
            SELECT {table}.pid AS id, members.plan
            FROM (
                SELECT *, ROW_NUMBER() OVER (ORDER BY UUID()) AS rand
                FROM members
            ) members
            JOIN {table} ON {table}.pid = members.rand
        ) AS assignment
        WHERE assignment.id = {table}.pid
    """)
    duckdb.sql("DROP TABLE members")
    duckdb.sql(f"UPDATE {units.table} SET pid = -1 WHERE pid > {num_participants}")



def assign_units(units, plans):
    """
    Assigns participants (units) to different plans in a balanced manner.
    Ensures that the number of participants is evenly distributed across all plans.

    Parameters:
    units : object
        An object containing participant data and metadata.
    plans : object
        An object containing plan assignment logic.
    """
    
    # Evaluate the units object to ensure it's up-to-date
    table = units.get_table()
    plans = determine_plans(units, plans)
    num_plans = len(plans)  # Total number of available plans
    num_participants = len(units)  # Total number of participants

    if num_plans:
        construct_assignment_table(table, units, num_plans, num_participants)
    
   
def assign_counterbalance(units, plans, parent = None):
    if parent is not None:
        assign_subunits(units, parent)
    else:
        assign_units(units, plans)
        
    # NOTE: assign subunits to the same plan as their parent unit was assigned to 
    if isinstance(units, Clusters):
        assign_counterbalance(units.units, plans, parent = units)


def assign(units, plans):
    return Assignment(units, plans)


       