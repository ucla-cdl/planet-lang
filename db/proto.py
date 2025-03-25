import duckdb


def no_repeat_inner(aliases):
    exps = []
    for i in range(len(aliases)):
        for j in range(i+1, len(aliases)):
            exps.append(aliases[i] + ".id" + " != " + aliases[j] + ".id")

    return " and ".join(exps)

def self_join(n, table):
    aliases = [table[0] + f"{i}" for i in range(1, n+1)]
    
    ids = [alias + ".id " + alias for alias in aliases]
    cross = [table + " " + alias for alias in aliases]
    
    return "INSERT INTO orders select nextval('id'), " + ", ".join(ids) + " from " + ", ".join(cross)

# def new_table(n, table):
#     "CREATE TABLE conditions (id integer primary key, iv1 VARCHAR, iv2 VARCHAR)"

def order(n, table):
    return self_join(n, table)

def filter(order, constraints):
    duckdb.sql("CREATE SEQUENCE id START 1;")
    duckdb.sql("CREATE TABLE conditions (id integer primary key, iv1 VARCHAR, iv2 VARCHAR)")
    duckdb.sql("insert into  conditions SELECT nextval('id'), iv1.level iv1, iv2.level iv2 into conditions from iv1, iv2")

    duckdb.sql("select * from conditions").show()

    duckdb.sql("DROP SEQUENCE id")
    duckdb.sql("CREATE SEQUENCE id START 1;")
    # need to do this dynamically 
    duckdb.sql("CREATE TABLE orders (id integer primary key, c1 VARCHAR, c2 VARCHAR, c3 VARCHAR, c4 VARCHAR)")

 
    duckdb.sql(order + " where " + " and ".join(constraints))

def assign(units, plans):
    num_plans = duckdb.sql("select COUNT(*) from orders").fetchall()[0][0]
    duckdb.sql(f"select * from {plans}").show()
    duckdb.sql(f"update participants set plan = floor(random() * {num_plans}) + 1")
    # duckdb.sql("select * from participants order by random() limit 3").show()
    duckdb.sql(f"select * from {units}").show()
    # duckdb.sql("SELECT test.pid, plan FROM (SELECT row_number() OVER (ORDER BY random()) as id, pid FROM participants ORDER BY RANDOM()) test join participants secondary on secondary.pid = test.pid").show()

def units(n):
    duckdb.sql("create table participants ( pid int, plan int )")
    for i in range(n):
        duckdb.sql(f"insert into participants values ({i+1}, 0)")


variables = {}

def variable(name, levels):
    variables[name] = levels

    duckdb.sql("CREATE TABLE " + name + " (level VARCHAR)")
    for level in levels:
        duckdb.sql("INSERT into " + name + f" VALUES ('{level}')")


def no_repeat(order):
    return filter(order, [no_repeat_inner(["c1", "c2", "c3", "c4"]),  
                                "c1.iv1 == \'a\'", # FIXME
                                "c2.iv1 == \'a\'"]) #FIXME


def pick_n(n, vars):
    return order(n, "conditions")




# declare independent variables in the experiment and their associated values
tool = variable("tool", levels = ["ffl", "latex"])
number = variable("number", levels = ["1", "2"])
task = variable("type", levels = ["creation", "editing"])

participants = units(28)

# possible ways to order two values of the tool variable 
# st. the value does not repeat in the order 
tool_order = no_repeat(pick_n(2, tool)) # -> [ffl, latex], [latex, ffl]
# possible ways to order two values of the number variable 
# st. the value does not repeat in the order 
number_order = no_repeat(pick_n(2, number)) # -> [1, 2], [2, 1]

task_order = start_with("creation", no_repeat(pick_n(2, task))) # -> [creation, editing]

# possible orders by overlaying every tool order with every number order
tool_number_orders = cross(tool_order, number_order) # -> [ffl-1, latex-2], [ffl-2, latex-1], [latex-1, ffl-2], [ffl-2, latex-2]

# nest orders of tool and task within the each value of every task order
orders = nest(task_order, tool_number_orders) 
# -> 1. [c-ffl-1, c-latex-2, e-ffl-1, e-latex-2], 
# 2. [c-ffl-2, c-latex-1, e-ffl-2, e-latex-1], 
# 3. [c-latex-1, c-ffl-2, e-latex-1, e-ffl-2], 
# 4. [c-ffl-2, c-latex-2, e-ffl-2, e-latex-2]


                        
assign(participants, order)









# declare independent variables in the experiment and their associated values
tool = variable("tool", levels = ["ffl", "latex"])
number = variable("number", levels = ["1", "2"])
task = variable("type", levels = ["creation", "editing"])

participants = units(28)


# possible ways to order two values of the tool variable 
# st. the value does not repeat in the order 
tool_order = no_repeat(pick_n(2, tool)) # -> [ffl, latex], [latex, ffl]
# possible ways to order two values of the number variable 
# st. the value does not repeat in the order 
number_order = no_repeat(pick_n(2, number)) # -> [1, 2], [2, 1]

task_order = no_repeat(pick_n(2, task)).require(start_with("creation")) # -> [creation, editing]

# possible orders by overlaying every tool order with every number order
tool_number_orders = cross(tool_order, number_order) # -> [ffl-1, latex-2], [ffl-2, latex-1], [latex-1, ffl-2], [ffl-2, latex-2]

# nest orders of tool and task within the each value of every task order
orders = nest(task_order, tool_number_orders) 
# -> 1. [c-ffl-1, c-latex-2, e-ffl-1, e-latex-2], 
# 2. [c-ffl-2, c-latex-1, e-ffl-2, e-latex-1], 
# 3. [c-latex-1, c-ffl-2, e-latex-1, e-ffl-2], 
# 4. [c-ffl-2, c-latex-2, e-ffl-2, e-latex-2]


                        
assign(participants, order)








# fully counterbalanced example

tool = variable("tool", levels = ["ffl", "latex"])
number = variable("number", levels = ["1", "2"])
task = variable("type", levels = ["creation", "editing"])

participants = units(28)

tool_order = no_repeat(pick_n(8, cross(tool, cross(number, task)))) 
                        
assign(participants, order)




# fully counterbalanced example

tool = variable("tool", levels = ["ffl", "latex"])
number = variable("number", levels = ["1", "2"])
task = variable("type", levels = ["creation", "editing"])

participants = units(28)

tool_order = no_repeat(pick_n(8, cross(tool, number, task])))
                        
assign(participants, order)



