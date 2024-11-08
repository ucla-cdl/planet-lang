import itertools


class Unit:
    def __init__(self, description):
        self.desc = description

class Units:
    def __init__(self):
        self.units = []

    def create(self, n, attributes):
        self.units = [Unit(attr) for attr in attributes for _ in range(n)]
        return self.units

class UnitFeature:
    def __init__(self, name):
        self.name = name
        self.levels= []

    def set_levels(self, levels):
        self.levels = [f"{self.name}-{i}" for i in range(levels)]

def combine(*argv):
    features = [arg.levels for arg in argv]
    comb = list(itertools.product(*features))
    return comb











# participant should be it's own class?
pid = UnitFeature("pid")
pid.set_levels(4)

time = UnitFeature("time_interval")
time.set_levels(4)

"""units with 2 features: pid and time interval"""
units = Units()
units.create(1, combine(pid, time)) # create 16 units 

""""constraint-based construction? I'm not sure if this makes sense 
because the sample is something that is set... """










""""notice that this looks like orthogonal array representation
of a latin sqaure without the sumbols :)"""
count = 1
for unit in units.units:
    print(f"unit {count}: {unit.desc}")
    count += 1




# constraint-based definition?



# """create 16 units such that each unit is a unique combination of unit features""" 
# units.create(16, unique=True)




# treatments = ("a", "b", "c", "d")


# assignment = Assignment(treatments, units)

# """ assign treatments to units such that the conditions at a given time interval 
# are different from each other and the treatments for a given pid are different """
# assignment.unique_conditon(wrt=pid)
# assignment.unique_conditon(wrt=time_interval)

# assignment.generate() # NOTE: should be latin square 


