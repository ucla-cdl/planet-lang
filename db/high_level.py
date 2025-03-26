"""Between Subjects"""
# Approach 1
exp = Experiment()
iv1 = variable("iv1", ["a", "b"]) # a variable with 2 levels

design = (
    between_subjects_design(exp, variables=iv1) # every participant sees exactly one level of the variable
    .assign_subjects(24) # 24 subjects in the study
    .randomize_runs() # randomly assign variable level to subject
)

exp.run()




# 2
exp = Experiment()
iv1 = between_subject_variable("iv1", ["a", "b"]) # a variable with 2 levels

# assign subjects to one level of the variable
design = (
    design(exp) 
    .subjects(24)
    .assign(iv1)
    .randomize_runs()
)
exp.run()




# 5
exp = Experiment()
iv1 = variable("iv1", ["a", "b"])

design = (
    design(exp)
    .assign_subjects(24)
    .between_subjects(iv1)
    .randomize_runs()
)
exp.run()




# 3 
iv1 = variable("iv1", ["a", "b"])
participants = units(24)

plans = between_subjects(iv1)

assign(participants, plans)





# 4 (close to primitives)
iv1 = variable("iv1", ["a", "b"])
plans = pick_n(1, iv1)
participants = units(24)

assign(participants, plans)












"""factorial designs"""
# factorial btw. subjects
exp = Experiment()
iv1 = between_subject_variable("iv1", ["a", "b"])
iv2 = between_subject_variable("iv2", ["c", "d"])

design = (
    factorial_design(exp, variables=[iv1, iv2])
    .assign_subjects(24)
    .randomize_runs()
)

exp.assign()




# 2
exp = Experiment()
iv1 = variable("iv1", ["a", "b"])
iv2 = variable("iv2", ["c", "d"])

design = (
    factorial_design(exp)
    .between_subjects([iv1, iv2])
    .assign_subjects(24)
    .randomize_runs()
)

exp.assign()




# factorial within subjects 
exp = Experiment()
iv1 = variable("iv1", ["a", "b"])
iv2 = variable("iv2", ["c", "d"])

design = (
    factorial_design(exp, variables=[iv1, iv2])
    .assign_subjects(24)
    .counterbalance([iv1, iv2])
    .randomize_runs()
)

exp.assign()






# alt. 3
exp = Experiment()
iv1 = variable("iv1", ["a", "b"])
iv2 = variable("iv2", ["c", "d"])
combined_variable = iv1 * iv2   # alternative to operator overloading

design = (
    design(exp, variable=combined_variable)
    .assign_subjects(24)
    .counterbalance(combined_variable)
    .randomize_runs()
)

exp.assign()



# 4 (close to primitives)
iv1 = variable("iv1", ["a", "b"])
iv2 = variable("iv2", ["c", "d"])

plans = cross(iv1, iv2)
participants = units(24)

assign(participants, plans)










# Fully Counterbalanced Within Subjects
# approach 1
iv1 = variable("iv1", ["a", "b"])
participants = units(24)

plans = counterbalance(within_subjects(iv1)) 

assign(participants, plans)







# approach 2 (closer to primitives)
iv1 = variable("iv1", ["a", "b"])

participants = units(24)

orders = no_repeat(pick_n(2, [iv1])) 

assign(participants, orders)








# approach 3
exp = Experiment()
iv1 = within_subject_variable("iv1", ["a", "b"])

design = (
    design(exp, variable=iv1)
    .assign_subjects(24)
    .randomize_runs()
    .counterbalance(iv1)
)

exp.run()







# approach 4
exp = Experiment()
iv1 = variable("iv1", ["a", "b"])

design = (
    within_subjects_design(exp, variable=iv1)
    .assign_subjects(24)
    .counterbalance(iv1)
    .randomize_runs()
)

exp.assign()







# 5 
exp = Experiment()
iv1 = variable("iv1", ["a", "b"])

design = (
    design(exp)
    .assign_subjects(24)
    .within_subjects(iv1)
    .counterbalance(iv1)
    .randomize_runs()
)

exp.assign()








# 5 
exp = Experiment()
iv1 = variable("iv1", ["a", "b"]).within_subjects().counterbalance()

design = (
    design(exp, variable = iv1)
    .assign_subjects(24)
    .randomize_runs()
)

exp.run()











"""Latin Square"""
exp = Experiment()
iv1 = variable("iv1", ["a", "b", "c"]).within_subjects().balance(n = 3)

units = units(24)

design = (
    design(exp, variable=iv1)
    .assign_subjects(units)
    .randomize_runs()
)

exp.run()






# approach 2
exp = Experiment()
iv1 = variable("iv1", ["a", "b"])


design = (
    design(exp)
    .assign_subjects(24)
    .within_subjects(iv1)
    .balance(iv1)
    .minimize_plans()
    .randomize_runs()
)

exp.run()







# approach 3
exp = Experiment()
iv1 = variable("iv1", ["a", "b"])


design = (
    design(exp)
    .assign_subjects(24)
    .within_subjects(iv1)
    .balance(iv1, n = 2)
    .randomize_runs()
)

exp.run()







# approach 3
exp = Experiment()
iv1 = variable("iv1", ["a", "b"])


design = (
    design(exp)
    .assign_subjects(24)
    .within_subjects(iv1)
    .balance(iv1)
    .num_plans(2)
    .randomize_runs()
)

exp.run()






""" Mixed Design """

# Approach 1
exp = Experiment()
iv1 = variable("iv1", ["a", "b"])
iv2 = variable("iv2", ["c", "d"])

design = (
    mixed_design(exp, variables=[iv1,iv2])
    .assign_subjects(24)
    .within_subjects(iv2)
    .counterbalance(iv2)
    .between_subjects(iv1)
    .randomize_runs()
)
exp.assign()








# 2
exp = Experiment()
iv1 = variable("iv1", ["a", "b"])
iv2 = variable("iv2", ["c", "d"])

design = (
    design(exp, variables=[iv1,iv2])
    .assign_subjects(24)
    .within_subjects(iv2)
    .counterbalance(iv2)
    .between_subjects(iv1)
    .randomize_runs()
)
exp.assign()










"""cluster assignment"""

# 1
exp = Experiment()
iv1 = variable("iv1", ["a", "b"])

units = units(24)
clusters = cluster(units, n = 4).randomize()

design = (
    betweebn_subjects_design(exp, variable = iv1)
    .assign(clusters)
    .randomize_runs()
)

exp.run()






# 2 
exp = Experiment()
iv1 = variable("iv1", ["a", "b"])

units = units(24)
clusters = cluster(units, n = 4).randomize()

design = (
   design(exp)
    .assign(clusters)
    .between_subjects(iv1)
    .randomize_runs()
)

exp.run()





# 3
exp = Experiment()
iv1 = variable("iv1", ["a", "b"])

units = units(24)

design = (
   design(exp)
    .cluster(units, 4) # something missing here 
    .between_subjects(iv1)
    .randomize_runs()
)

exp.run()



















exp = Experiment()
iv1 = within_subject_variable("iv1", ["a", "b"])
iv2 = within_subject_variable("iv2", ["c", "d"])

design = (
    mixed_design(exp)
    .assign_subjects(24)
    .counterbalance(iv1)
    .counterbalance(iv2)
    .nest(iv1, iv2)
    .randomize_runs()
)

exp.assign()


exp = Experiment()
iv1 = variable("iv1", ["a", "b"]).counterbalance()
iv2 = variable("iv2", ["c", "d"]).counterbalance()

design = (
    mixed_design(exp)
    .assign_subjects(24)
    .nest(iv1, iv2)
    .randomize_runs()
)

exp.assign()







iv1 = variable("iv1", ["a", "b"])
iv2 = variable("iv2", ["c", "d"])

participants = units(24)

orders1 = no_repeat(pick_n(2, [iv1])) 
orders2 = no_repeat(pick_n(2, [iv2])) 

orders = nest(orders1, orders2)

assign_counterbalance(participants, orders)


# alt
exp = Experiment()
iv1 = variable("iv1", ["a", "b"]).counterbalance()

iv2 = (
        variable("iv2", ["c", "d"])
        .within_subjects()
        .counterbalance()
        .nest(iv1)
    )


design = (
    factorial_design(exp, variables=iv2)
    .assign_subjects(24)
    .within_subjects(iv2)
    .randomize_runs()
)

exp.assign()























# between subjects
exp = Experiment()
treatment = variable("treatment", ["drug", "placebo"])
units = units(24)

design = (
    design(exp)
    .assign_to(units)
    .between_subjects(treatment)
    .randomize()
)
exp.run()


# compare to 


# primitives
treatment = variable("treatment", ["drug", "placebo"])
participants = units(24)



assign(participants, treatment)









# within subjects
exp = Experiment()
treatment = variable("treatment", ["drug", "placebo"])

units = units(24)

design = (
    design(exp)
    .assign_to(units)
    .within_subjects(treatment, num_trials = 4)
    .counterbalance() # implicit n = 1
    .randomize()
)
exp.run()


# compare to 


# primitives
treatment = variable("treatment", ["drug", "placebo"])
treatment_order = no_repeat(pick_n(2, treatment)) # within subjects, full counterbalance
participants = units(24)

assign(participants, treatment_order)







# latin-square
exp = Experiment()
treatment = variable("treatment", ["drug1", "drug2", "placebo"])

units = units(24)

design = (
    design(exp)
    .assign_to(units)
    .within_subjects(treatment)
    .partial_counterbalance() # counterbalance, but minimize the number of orders
    .randomize()
)
exp.run()

# separate class of functions 
# conjunction of filters for columns and rows 
# FUNCTION THAT returns this value as a flag 


# compare to 


# primitives
treatment = variable("treatment", ["drug", "placebo"])

# something not working/missing here
treatment_order = no_repeat(
            no_repeat(
                pick_n(2, iv1)
            ), 
            axis=1 # no repeat accross columns
        )
participants = units(24)

assign(participants, plans)




# mixed design
exp = Experiment()
treatment = variable("treatment", ["drug", "placebo"])
task = variable("task", ["run", "walk"])

units = units(24)

design = (
    design(exp) # automatic nest
    .assign_to(units)
    .within_subjects(task)
    .counterbalance(task)
    .between_subjects(treatment)
)
exp.run()

# selector: modify treatment*
# compare to 

# each time interval is like a between subjects study 
# units are the trials 


# primitives
treatment = variable("treatment", ["drug", "placebo"])
task = variable("task", ["run", "walk"])
participants = units(24)

task_plans = no_repeat(pick_n(2, task)) # within subject
task_treatment_order = nest(treatment, treatment_plans) # mixed design

assign(participants, task_treatment_order)




# cluster assignment between subjects
exp = Experiment()
treatment = variable("treatment", ["drug", "placebo"])
units = units(24)

clusters = (
        clusters(4)
        .from(units)
        .randomize() # this doesn't really work with the new assignment procedure for the design
)       

design = (
   design(exp)
    .assign_to(clusters, method=random()) 
    .between_subjects(treatment)
)

exp.assign()

# cluster assignment between subjects
exp = Experiment()
treatment = variable("treatment", ["drug", "placebo"])
units = units(24)

clusters = (
        clusters()
        .assign(units, method=random())
        .num_clusters(n=4)
)       

design = (
   design(exp)
    .assign_to(clusters, method=random()) 
    .between_subjects(treatment)
)

exp.assign()

# cluster assignment between subjects
exp = Experiment()
treatment = variable("treatment", ["drug", "placebo"])
units = units(24)

groups = partition(units, n = 4, method = random())

design = (
   design(exp)
    .assign_to(clusters, method=random()) 
    .between_subjects(treatment)
)

exp.assign()

# cluster assignment between subjects
exp = Experiment()
treatment = variable("treatment", ["drug", "placebo"])
clusters = clusters(4)
units = units(24)
units.assign_to(clusters, method = random())

groups = partition(units, n = 4, method = random())

design = (
   design(exp)
    .assign_to(clusters, method=random()) 
    .between_subjects(treatment)
)

exp.assign()


# compare to 


# primitives
treatment = variable("treatment", ["drug", "placebo"])
participants = units(24)

# needs work
participant_groups = randomize(cluster(4, subunits = participants))

assign(participant_groups, treatment)




# factorial 


# factorial within subjects 
exp = Experiment()
treatment = variable("treatment", ["drug", "placebo"])
task = variable("task", ["run", "walk"])

design = (
    factorial_design(exp) # implicit creation of new combined conditions
    .assign_subjects(24)
    .within_subjects([treatment, task]) # unit sees every possible combination of the two variables
    .counterbalance([treatment, task]) 
    .randomize_runs()
)

exp.assign()



# compare to 


# explicit variable creation
exp = Experiment()
treatment = variable("treatment", levels = ["drug", "placebo"])
task = variable("task", levels = ["run", "walk"])

# NOTE: this is like saying, create a new variable task-treatment, where the level 
# is every combination of the individualt variable 
# for example: 
#      treatment_task = variable("treatment_task", ["drug-run", "drug-walk", "placebo-run", "placebo-walk"])
multi_factorial_var = factorial([treatment, task]) # combines every level of both variables

participants = units(24)

design = (
    design(exp)
    .assign_to(units)
    .within_subjects(multi_factorial_var)
    .counterbalance(multi_factorial_var)
    .randomize_runs()
)

exp.assign()



# compare to 



# primitives
treatment = variable("treatment", ["drug", "placebo"])
task = variable("task", ["run", "walk"])

treatment_and_task = cross(treatment, task) # combines every level of both variables
participants = units(24)

assign(participants, treatment_and_task)



# alt
treatment = variable("treatment", ["drug", "placebo"])
task = variable("task", ["run", "walk"])

treatment_and_task = variable([treatment, task])
participants = units(24)

assign(participants, treatment_and_task)












# factorial within subjects 
exp = Experiment()
treatment = variable("treatment", ["drug", "placebo"])
task = variable("task", ["run", "walk"])

design = (
    design(exp) # implicit creation of new combined conditions
    .assign_subjects(24)
    .within_subjects(treatment, task, num_trials = 2) # unit sees every possible combination of the two variables
    .counterbalance(treatment) 
    .counterbalance(task) 
    .randomize_runs()
)

exp.assign()






# factorial within subjects 
exp = Experiment()
treatment = variable("treatment", ["drug", "placebo"])
task = variable("task", ["run", "walk"])

design = (
    design(exp) # implicit creation of new combined conditions
    .assign_subjects(24)
    .within_subjects(treatment, task, num_trials = 2) # unit sees every possible combination of the two variables
    .counterbalance(treatment, task) 
    .exclusive_match("drug", "walk")
    .randomize_runs()
)

exp.assign()








# factorial within subjects 
exp = Experiment()
treatment = variable("treatment", ["drug", "placebo"])
task = variable("task", ["run", "walk"])

design = (
    design(exp) # implicit creation of new combined conditions
    .assign_subjects(24)
    .within_subjects(treatment, task, num_trials = 2) # unit sees every possible combination of the two variables
    .counterbalance(treatment, task) 
    .exclusive_match("drug", "walk")
    .randomize_runs()
)


nested_design = (
    design(exp) # implicit creation of new combined conditions
    .nest(design)
    .assign_subjects(24)
    .within_subjects(interface) # unit sees every possible combination of the two variables
    .counterbalance(interface) 
    .randomize_runs()
)

exp.assign()



















# mixed design
exp = Experiment()
treatment = variable("treatment", ["drug", "placebo"])
task = variable("task", ["run", "walk"])

units = units(24)

design = (
    design(exp) 
    .assign_to(units)
    .randomize()
)

design.append(treatment).within_subjects(num_trials = 2).counterbalance()
design.variable = treatment.within_subjects(num_trials = 2).counterbalance()
design.append(task).between_subjects()


exp.run()