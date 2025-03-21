from z3 import *
from .blocks import BlockFactor
from .constraint import OccurNTimes
from .constraint import AllMatch, Majority, Distinguish, NeverOccurTogether, AlwaysOccurTogether
import duckdb

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
        self.table = table

    def add_attribute(self, attr):

        assert isinstance(attr, BlockFactor)
        self.attributes.append(attr)

    

    def eval(self):
        duckdb.sql(f"create table {self.table} ( pid int, plan int )")
        for i in range(self.n):
            duckdb.sql(f"insert into {self.table} values ({i+1}, 0)")

        duckdb.sql(f"select * from {self.table}").show()

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

    def eval(self):
        self.units.eval()
        super().eval()

        duckdb.sql(f"""ALTER TABLE {self.table}
                        ADD subunits INTEGER[]""")
        
        duckdb.sql(f"select * from {self.table}").show()
     
     
        limit = int(self.units.n/self.n)
        for i in range(1, self.n+1):   
            
            duckdb.sql(f"""update {self.table} set subunits = (select array_agg(units.pid) from 
                                    (select      *, 
                                                row_number() over(order by uuid()) rand
                                    from        {self.units.table} where pid not in (select unnest(subunits) from {self.table} ) limit {limit}) units)
                                    
                                    where pid = {i}""")
            
        
        duckdb.sql(f"select * from {self.table}").show()



       

# inherit from variable? 
class Participants(Units):
    """ a Unit represents a singular unit that participates in a study. Units
            get randomly assigned to an experimental group during assignment

    n: id of the unit
    """
    def __init__(self, n=0):
        Units.__init__(self, n)

    def distinguish(self, dim):
        constraint = Distinguish(dim)
        self.constraints.append(constraint)

    def never_occur_together(self):
        constraint = NeverOccurTogether(self)
        self.constraints.append(constraint)

    def always_occur_together(self):
        constraint = AlwaysOccurTogether(self)
        self.constraints.append(constraint)

# inherit from variable? 
class Groups(Units):
    """ a Unit represents a singular unit that participates in a study. Units
            get randomly assigned to an experimental group during assignment

    n: id of the unit
    """
    def __init__(self, n, labels = None):
        Units.__init__(self, n)
        self.groups = [Group(i) for i in range(n)]

    def expand_groups(self, num_groups):
  
        assert num_groups % self.n == 0
        
        new_groups = Groups(num_groups)
        for attr in self.attributes:

            new_groups.add_attribute(attr)
        return new_groups
    


class Group:
    def __init__(self, n):
        self.n = n
        self.labels = []

    def add_label(self, label):
        self.labels.append(label)

    



        
    
