from z3 import *
from .variable import Exact, Any, Different, Match
from.helpers import DEBUG

# Condition represents one possible "total condition" 
# pass in metaconditions to construct Condition, 
# along with constraints on the condition
class ExperimentCondition():
    # argv consists of Variable types
    def __init__(self, *argv):
        self.var_to_z3 = {} # dict stores var to the constrained options 
        for arg in argv:
            # arg is a Z3Var type with Different, or Match wrapper 
            # arg.var is a and instance of a Variable object
            self.var_to_z3[arg.var] = arg

        # probably change this name... stores what we need 
        # to add to the solver based on the constraints
        # but we add to the solver in condition order...
        self.solver = z3.Solver()
        self.evaluation = None
        self.name = self.__class__

    def add_name(self, name):
        self.name = name
     


    # change this from eval to a solver constructor 
    # call equivilant in constructor 
    def eval(self):
        # the way we represent each class in z3 is different
        # based on class wrapper... # check if instance and then 
        # append proper Z3 class based on variables
        # messy messy code :(
        s = self.solver
        for var in self.var_to_z3:
            s.push()

            if isinstance(self.var_to_z3[var], Exact) or isinstance(self.var_to_z3[var], Any):
                DEBUG("variable " + str(var) + " does not depend on any previous conditions")
                print("\t" + str(self.var_to_z3[var]))

                s.add(self.var_to_z3[var].__z3__)
                if s.check() == sat:
                    m = s.model()
                self.var_to_z3[var].test = m

                print("\teval: " + str(m))

            if isinstance(self.var_to_z3[var], Different):
                DEBUG("variable " + str(var) + " depends on " + str(self.var_to_z3[var].condition))
                # left off here: need to get the evaluated model
                # and make sure that the values do not reflect this 
                s.add(self.var_to_z3[var].condition.var_to_z3[var].__z3__)
                m = self.var_to_z3[var].condition.var_to_z3[var].test

                print("\tnot: ", m)

                for v in m:
                    # variable does not equal it's current value
                    s.add((v() != True))

                if s.check() == sat:
                    m = s.model()
                    print("\teval: " + str(m))

                self.var_to_z3[var].test = m


            if isinstance(self.var_to_z3[var], Match):
                DEBUG("variable " + str(var) + " depends on " + str(self.var_to_z3[var].condition))

                m = self.var_to_z3[var].condition.var_to_z3[var].test

                print("\tmatch: ", m)

                self.var_to_z3[var].test = m
                
                print("\teval: " + str(m))

            s.pop()

   

        DEBUG("")
        return "test"
                

  
    def __str__(self):
        return str(self.name)
    
class ConditionTest:
    def __init__(self, *argv):
    

        self.name = __class__

    def add_name(self, name):
        self.name = name

    def __str__(self):
        return str(self.name)