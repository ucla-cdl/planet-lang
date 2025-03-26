import duckdb


num_conditions_tables = 0
num_orders_tables = 0

def assign(units, plans):
    num_plans = duckdb.sql("select COUNT(*) from orders").fetchall()[0][0]
    

    duckdb.sql(f"select * from {plans}").show()
    duckdb.sql(f"update participants set plan = floor(random() * {num_plans}) + 1")
    # duckdb.sql("select * from participants order by random() limit 3").show()
    duckdb.sql(f"select * from {units}").show()
    # duckdb.sql("SELECT test.pid, plan FROM (SELECT row_number() OVER (ORDER BY random()) as id, pid FROM participants ORDER BY RANDOM()) test join participants secondary on secondary.pid = test.pid").show()

    duckdb.sql(f"select count(*) from {units} group by plan").show()



def test_self_join(n, table):
    aliases = [table[0] + f"{i}" for i in range(1, n+1)]
    
    ids = [alias + ".id " + alias for alias in aliases]
    cross = [table + " " + alias for alias in aliases]
    
    return f"select nextval('id'), " + ", ".join(ids) + " from " + ", ".join(cross)

def limit(n, orders):
    duckdb.sql(test_self_join(n, orders)).show()

def assign_counterbalance(units, plans):
    units.eval()
    plans.eval()


    num_plans = duckdb.sql(f"select COUNT(*) from orders{plans.id}").fetchall()[0][0]
    num_participants = duckdb.sql("select COUNT(*) from participants").fetchall()[0][0]
    duckdb.sql("CREATE TABLE members (plan int)")

    
    num_per_group = int(num_participants / num_plans)
    
    for i in range(1, num_plans+1):
        for _ in range(1, num_per_group+1):
            duckdb.sql(f"insert into members values ({i})")

    duckdb.sql(""" select participants.pid, members.plan from 
                                (select      *, 
                                            row_number() over(order by uuid()) rand
                                from        members) members, participants
               where participants.pid = members.rand
                        
           """).show()
    
    
    

    duckdb.sql(""" select count(*) from (select participants.pid, members.plan from 
                                (select      *, 
                                            row_number() over(order by uuid()) rand
                                from        members) members, participants
               where participants.pid = members.rand) group by plan
                        
           """).show()
    
    duckdb.sql(f"select * from conditions{plans.id}").show()
    duckdb.sql(f"select * from orders{plans.id}").show()
    



def no_repeat_inner(aliases):
    exps = []
    for i in range(len(aliases)):
        for j in range(i+1, len(aliases)):
            exps.append(aliases[i] + ".id" + " != " + aliases[j] + ".id")

    return " and ".join(exps)

def self_join(n, table, sym):
    aliases = [table[0] + f"{i}" for i in range(1, n+1)]
    
    ids = [alias + ".id " + alias for alias in aliases]
    cross = [table + " " + alias for alias in aliases]
    
    return f"INSERT INTO orders{sym} select nextval('id'), " + ", ".join(ids) + " from " + ", ".join(cross)


class Units:
    def __init__(self, n):
        self.n = n

    def eval(self):
        duckdb.sql("create table participants ( pid int, plan int )")
        for i in range(self.n):
            duckdb.sql(f"insert into participants values ({i+1}, 0)")

def filter(order, constraints):
    order.filter(constraints)
    return order

def no_repeat(order):
    return filter(order, [no_repeat_inner(order.get_column_names())])
                                

def pick_n(n, vars):
    temp = Order(n, vars)
    return temp


def nest(o1, o2):
    n = o1.n * o2.n
    variables = o1.variable_list + o2.variable_list
    order = pick_n(n, variables)

    no_repeat(order)

    for i in range(o1.n):
        filter(order, [no_repeat_inner(order.get_column_names()[i*o2.n:o2.n*(i+1)])])

    cols = order.get_column_names()
    vname1 = o1.variable_list[0].name
    vname2 = o2.variable_list[0].name

    
    for i in range(o1.n-1):
        for j in range(o2.n):
            filter(order, [f"{cols[(i*o2.n) + j]}.{vname2} = {cols[j+((1+i)*o2.n)]}.{vname2}"])

 
    # outer match
    for i in range(o1.n):
        for j in range(o2.n-1):
            filter(order, [f"{cols[(i*o2.n) + j]}.{vname1} = {cols[(j+1)+(i*o2.n)]}.{vname1}"])

    return order

def cross(o1, o2):
    assert o1.n == o2.n

    n = o1.n
    variables = o1.variable_list + o2.variable_list
    order = pick_n(n, variables)

    cols = order.get_column_names()
    vname1 = o1.variable_list[0].name
    vname2 = o2.variable_list[0].name

    for i in range(n):
        for j in range(n):
            if i != j:
                filter(order, [f"{cols[i]}.{vname1} != {cols[j]}.{vname1}"])
                filter(order, [f"{cols[i]}.{vname2} != {cols[j]}.{vname2}"])

    return order

def units(n):
    return Units(n)

def alloc_sequence():
    return "CREATE SEQUENCE id START 1;"

def free_sequence():
    return "DROP SEQUENCE id;"

class Order:
    def __init__(self, n, variable_list):
        self.n = n # number of trials
        self.variable_list = variable_list # variables involved in order
        self.constraints = [] # filters to apply
        self.evaled = False # just-in-time eval

        # FIXME: shouldn't be dependent on global variable
        global num_conditions_tables
        self.id = num_conditions_tables + 1
        num_conditions_tables += 1
        
    def eval(self):
        if not self.evaled:
            for v in self.variable_list:
                v.eval()

            query = self._create_query()

            duckdb.sql(query)
            self.evaled = True

    def order(self):
            return self_join(self.n, f"conditions{self.id}", self.id)
    
    def construct_constraints(self):
        return ",  where " + " and ".join(self.constraints)
    
    def create_orders(self):    
        cols = self.get_column_names()
        init_cols = [col + " VARCHAR" for col in cols]

        ret = ""
        # NOTE: need to do this dynamically 
        ret += f"CREATE TABLE orders{self.id} (id integer primary key, " + ", ".join(init_cols) + " );"
        return ret
    
    def create_conditions(self):
        variables = [self.variable_list[i].name for i in range(len(self.variable_list))]
        init_variables = [v + " VARCHAR" for v in variables]
        variable_level = [v + ".level " + v for v in variables]
        global num_conditions_tables

        ret = alloc_sequence()
        ret += f"CREATE TABLE conditions{self.id} (id integer primary key, " + ", ".join(init_variables) + ");"
        ret += f"insert into  conditions{self.id} SELECT nextval('id'), " + ", ".join(variable_level) + f" into conditions{self.id} from " + ", ".join(variables) + ";"
        ret += free_sequence()

        num_conditions_tables += 1
        return ret

    def _create_query(self):
        query = self.create_conditions()
        query += self.create_orders()

        query += alloc_sequence()
        query +=  self.order() + self.construct_constraints() + ";"
        query += free_sequence()

        return query

    
    def filter(self, constraints):
        self.constraints.extend(constraints)

    def get_column_names(self):
        return [f"c{i+1}" for i in range(self.n)]

    def __str__(self):
        if not self.evaled:
            self.eval()

        return str(duckdb.sql(f"select * from orders{self.id}").fetchdf())
    


class Variable:
    """
    Creates a variable table with an unique id and the
    name of the level of the user-defined variable. 
    """
    def __init__(self, name, levels):
        self.name = name # variable name
        self.levels = levels # assignment options

    def eval(self):
        # creates a table with rows representing each possible assignment value
        duckdb.sql("CREATE TABLE " + self.name + " (level VARCHAR)")
        # insert row where the value is the name of the level
        for level in self.levels:
            duckdb.sql("INSERT into " + self.name + f" VALUES ('{level}')")


def variable(name, levels):
    return Variable(name, levels)




# iv1 = variable("iv1", ["a", "b", "c"])
# iv2 = variable("iv2", ["d", "e", "f"])

# participants = units(36)

# orders1 = no_repeat(pick_n(3, [iv1])) 
# orders2 = no_repeat(pick_n(3, [iv2])) 

# orders = cross(orders1, orders2)

# assign_counterbalance(participants, orders)

# print(orders)




iv1 = variable("iv1", ["a", "b", "c"])
iv2 = variable("iv2", ["d", "e"])

participants = units(36)

orders1 = no_repeat(pick_n(3, [iv1])) 
orders2 = no_repeat(pick_n(2, [iv2])) 

orders = nest(orders1, orders2)

assign_counterbalance(participants, orders)

# print(orders)



# iv1 = variable("iv1", ["a", "b"])
# iv2 = variable("iv2", ["d", "e"])

# participants = units(36)

# orders = no_repeat(pick_n(4, [iv1, iv2])) 

# assign_counterbalance(participants, orders)

# print(orders)






# iv1 = variable("iv1", ["a", "b", "c"])

# participants = units(36)

# orders = no_repeat(pick_n(3, [iv1]))

# limit(3, orders)

# # assign_counterbalance(participants, orders)

# print(orders)












# levels = ["a", "b", "c"]
# duckdb.sql("CREATE TABLE conditions (level VARCHAR)")
# for level in levels:
#     duckdb.sql(f"INSERT into conditions VALUES ('{level}')")


    
# # come back to this for count costraint
# duckdb.sql("select * from conditions a, conditions b, conditions c where len(concat(a.level, b.level, c.level)) - len(replace(concat(a.level, b.level, c.level), 'a', '')) > 1 ;").show()

# duckdb.sql("CREATE SEQUENCE id START 1;")
# levels = ["a", "b", "c", "d", "e"]
# cols = [f"c{i+1}" for i in range(5)]
# init_cols = [col + " VARCHAR" for col in cols]
# duckdb.sql("CREATE TABLE conditions (level VARCHAR)")
# for level in levels:
#     duckdb.sql(f"INSERT into conditions VALUES ('{level}')")


# duckdb.sql("CREATE TABLE orders (id integer primary key, " + ", ".join(init_cols) + " );")


# ids = [alias + ".level " + alias for alias in cols]
# cross = [f"conditions c{i+1}" for i in range(5)]
    
# duckdb.sql(f"INSERT INTO orders select nextval('id'), " + ", ".join(ids) + " from " + ", ".join(cross))

# conditions = [f"conditions c{i+1}" for i in range(5)]


# duckdb.sql("select * from orders").show()

# conditions = [f"orders o{i+1}" for i in range(5)]
# duckdb.sql("select * from " + ",".join(conditions)).show()
