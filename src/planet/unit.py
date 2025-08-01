from z3 import *
from .blocks import BlockFactor
import duckdb
import time
from planet.candl import *

class Unit:
    """ a Unit represents a singular unit that participates in a study. Units
            get randomly assigned to an experimental group during assignment

    n: id of the unit
    """
    def __init__(self, n):
        self.n = n

class Units:
    def __init__(self, n, table = "participants"):
        self.n = n
        self.attributes = []
        self.hash = str(time.time()).replace(".", "")
        self.table = table + self.hash
        self.evaled = False

    def add_attribute(self, attr):

        assert isinstance(attr, BlockFactor)
        self.attributes.append(attr)

    
    def eval(self):
        if not self.evaled:
            duckdb.sql(f"create table {self.table} ( pid int, plan int )")
            for i in range(self.n):
                duckdb.sql(f"insert into {self.table} values ({i+1}, 0)")
            self.evaled = True

    def get_table(self):
        self.eval()
        return self.table

    def get_plan(self, n):
        return duckdb.execute(f"select plan from {self.table} where pid = {n}").fetchone()[0]

    def get_attributes(self):
        return self.attributes
    
    def __len__(self):
        return self.n 
    

class Clusters(Units):
    """A Cluster represents a group of Units that are grouped together for a specific purpose."""
    def __init__(self, units, n):
        assert units.n % n == 0
        super().__init__(n, "clusters")

        assert units is not None
        self.units = units

    def get_units(self, n):
        ret = duckdb.sql(f"select subunits from {self.table} where pid = {n}").fetchnumpy()["subunits"][0]
        return list(ret)

    def eval(self):
        self.units.eval()
        super().eval()

        duckdb.sql(f"""ALTER TABLE {self.table}
                        ADD subunits INTEGER[]""")
        
     
     
        limit = int(self.units.n/self.n)
        for i in range(1, self.n+1):   
            
            duckdb.sql(f"""update {self.table} set subunits = (select array_agg(units.pid) from 
                                    (select      *, 
                                                row_number() over(order by uuid()) rand
                                    from        {self.units.table} where pid not in (select unnest(subunits) from {self.table} ) limit {limit}) units)
                                    
                                    where pid = {i}""")
            



       

# inherit from variable? 
class Participants(Units):
    """ a Unit represents a singular unit that participates in a study. Units
            get randomly assigned to an experimental group during assignment

    n: id of the unit
    """
    def __init__(self, n=0):
        Units.__init__(self, n)

   

# inherit from variable? 
class Groups(Units):
    """ a Unit represents a singular unit that participates in a study. Units
            get randomly assigned to an experimental group during assignment

    n: id of the unit
    """
    def __init__(self, n=0):
        self.n = n

    def set_num_plans(self, n):
        self.n = n 
    
    def __len__(self):
        return self.n
    
    def extract_counterbalance_group(self, var):
        """Extract variables and condition count"""
        return (var.get_variables(), len(var))
    
    def calculate_num_plans(self, counterbalanced_groups, rankings, num_trials):
  
        """Determine the number of experimental plans based on constraints and trial width."""
        total_n_plans = 1

        for variables, num_conditions in counterbalanced_groups:
                num_trials = num_trials
                print(variables, num_conditions, num_trials)
                total_n_plans *= calculate_plan_multiplier(num_conditions, variables, num_trials)
                print(total_n_plans)
        for ranking in rankings:
            total_n_plans *= factorial_product_of_counts(ranking)

        self.set_num_plans((int(total_n_plans)))
        print("groups", self.n)
    




        
    
