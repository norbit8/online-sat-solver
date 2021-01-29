from __future__ import annotations

from parser_util.parser_helper import *
from prop_logic.semantics import *


def createDic(f, d, counter):
    phi_G = Formula("x" + str(counter))
    counter += 1
    d[f.id] = phi_G
    if (is_base_formula(f)) or is_variable(f.root):
        return counter
    elif (is_unary(f.root)):
        return createDic(f.first, d, counter)
    else:
        counter = createDic(f.first, d, counter)
        counter = createDic(f.second, d, counter)
        return counter


def createLis(f, d, lis):
    if (is_base_formula(f) or is_variable(f.root)):
        f_temp = Formula("<->", d[f.id], f)
        lis.append(f_temp)
        return
    if (is_unary(f.root)):
        temp = Formula(f.root, d[f.first.id])
        f_temp = Formula("<->", d[f.id], temp)
        lis.append(f_temp)
        createLis(f.first, d, lis)
    else:
        temp = Formula(f.root, d[f.first.id], d[f.second.id])
        f_temp = Formula("<->", d[f.id], temp)
        lis.append(f_temp)
        createLis(f.first, d, lis)
        createLis(f.second, d, lis)


def get_Tseitinis_list(phi):
    d = dict()
    lis = []
    counter = 0
    createDic(phi, d, counter)
    lis.append(d[phi.id])
    createLis(phi, d, lis)
    return lis, d


def get_literal_from_cnf(f):
    literals = []

    while (f.root == '|'):

        if (f.first.root == "~"):
            literals.append(f.first.root + f.first.first.root)
        else:
            literals.append(f.first.root)
        f = f.second

    if f.root == "~":
        literals.append(f.root + f.first.root)
    else:
        literals.append(f.root)

    return literals


def create_cnf_from_literals(l):
    if len(l) == 1:
        return Formula.parse(l[0])
    else:
        second = create_cnf_from_literals(l[1:])
        first = Formula.parse(l[0])
        return Formula("|", first, second)


def remove_literal_occurs_twice(f):
    literals = list(set(get_literal_from_cnf(f)))
    return create_cnf_from_literals(literals)


def is_clause_tautlogy(f):
    literals = list(set(get_literal_from_cnf(f)))
    for literal in literals:
        if literal[0] == "~":
            if literal[1:] in literals:
                return True
        else:
            if "~" + literal in literals:
                return True
    return False


def is_clause_BCP(clause, d):
    """
    checks whether only one var isnt assign
    :param clause:
    :param d:
    :return:
    """
    counter = 0
    for literal in clause:
        if literal[0] == "~":
            var = literal[1:]
            assign = False
        else:
            var = literal
            assign = True
        if var in d.keys():
            if not (d[var] ^ assign):
                return
        else:
            potenital_last_variable = var
            potenital_assign = assign
            counter += 1
        if counter > 1:
            return
    return (potenital_last_variable, potenital_assign)


def BCP(cnf, d):
    bcp_flag = True
    while bcp_flag:
        clause_flag = False
        for clause in cnf:
            t = is_clause_BCP(clause, d)
            if (t != None):
                clause_flag = True
                if t[0] in d.keys() and d[t[0]] != t[1]:
                    return False
                d[t[0]] = t[1]
        if not clause_flag:
            bcp_flag = False

    return True


def list_to_true_cnf(l):
    if len(l) == 1:
        return l[0]
    else:
        second = list_to_true_cnf(l[1:])
        first = l[0]
        return Formula("&", first, second)


def tseitinis_model(f, model, special_dic):
    if (is_base_formula(f)) or is_variable(f.root):
        model[special_dic[f.id].root] = evaluate(f, model)
    elif (is_unary(f.root)):
        tseitinis_model(f.first, model, special_dic)
        model[special_dic[f.id].root] = evaluate(f, model)
    else:
        tseitinis_model(f.first, model, special_dic)
        tseitinis_model(f.second, model, special_dic)
        model[special_dic[f.id].root] = evaluate(f, model)
    return model


def compare_formulas(input_formula, ts_formula, special_dict):
    """
    This method gets two formulas, one in regular form and the other one is the first one ts form
    and return True if the second formula is really the ts form of the first one.
    :param input_formula: Formula
    :param ts_formula: Formula that should be the ts form of the first input formula
    :return: True if ts_formula is the ts form of the input_formula
    """
    f_input_vars = Formula.variables(input_formula)
    models_original_formula = all_models(list(f_input_vars))
    for model in models_original_formula:
        result_original_formula = evaluate(input_formula, model)
        ts_model = tseitinis_model(input_formula, model, special_dict)
        result_ts_formula = evaluate(ts_formula, ts_model)
        if result_original_formula != result_ts_formula:
            return False
    return True


def parse(str):
    # Tseitini
    phi = Formula.parse(str)
    Tseitinis_list, special_dict = get_Tseitinis_list(phi)
    f = [remove_literal_occurs_twice(f) for f in convert_to_cnf(Tseitinis_list)]


    f1 = [c for c in f if not is_clause_tautlogy(c)]
    cnf = [Claus(f) for f in f1]
    return cnf, phi.variables(), phi


class Claus:
    def __init__(self, formula: Formula):
        self.formula = formula
        self.literals = self.convert_to_literals(formula)
        self.number_of_literals = len(self.literals)
        self.variables = list(self.formula.variables())
        self.possible_watch_literals = self.variables
        self.watch_literals = []
        self.is_satsfied = False

    def convert_to_literals(self, f):
        literals = []

        while (is_binary(f.root)):
            if (is_unary(f.first.root)):
                literals.append(f.first.root + f.first.first.root)
            else:
                literals.append(f.first.root)
            f = f.second
        if (is_unary(f.root)):
            literals.append(f.root + f.first.root)
        else:
            literals.append(f.root)
        return literals

    def get_last_one(self):
        if self.number_of_literals == 1:
            return self.literals[0][0] != "~"

    def conatin_variabe(self, variable: str):
        return variable in self.variables

    def get_one_watch_literal(self):
        if self.possible_watch_literals:
            return self.possible_watch_literals.pop(0)
        return []

    def get_two_watch_literals(self):
        return self.possible_watch_literals[:2]

    def is_bcp_potential(self, variable):
        # print("claus:", self.formula)
        # print(self.possible_watch_literals)
        # print(self.watch_literals)
        return len(self.possible_watch_literals) == 0 and len(list(set(self.watch_literals) - {variable})) == 1

    def get_new_watch_literal(self, variable):
        self.watch_literals.remove(variable)
        new_watch_literal = [self.get_one_watch_literal(), ]
        self.watch_literals += new_watch_literal
        return new_watch_literal[0]

    def get_literal(self, variable):
        for literal in self.literals:
            if variable in literal:
                return literal
        # error
        print("problem1")
        exit(1)

    def update_possible_literals(self, model):
        self.possible_watch_literals = [var for var in self.possible_watch_literals if var not in model.keys()]

    def all_false(self, model, variable):
        last_unassinged_literal = (set(self.watch_literals) - {variable}).pop()
        literal = self.get_literal(last_unassinged_literal)
        if literal[0] == '~':
            model[last_unassinged_literal] = True
        else:
            model[last_unassinged_literal] = False
        return not evaluate(self.formula, model)

    def get_bcp_assignment(self, variable):
        last_unassinged_literal = (set(self.watch_literals) - {variable}).pop()
        literal = self.get_literal(last_unassinged_literal)
        if literal[0] == '~':
            value = False
        else:
            value = True
        return last_unassinged_literal, value

    def __repr__(self):
        return str(self.literals)


class Literal:

    def __init__(self, variable_name: str, decision_level: int, assignment: bool):
        self.variable_name = variable_name
        self.decision_level = decision_level
        self.assignment = assignment

    def __eq__(self, other: Literal):
        return self.variable_name == other.variable_name

    def __hash__(self):
        return self.variable_name.__hash__()

    def __repr__(self):
        return self.variable_name




# phi = Formula.parse("(p0&(~p1&(~p2&p3)))")
# Tseitinis_list, special_dict = get_Tseitinis_list(phi)
# print(Tseitinis_list)
# for c in Tseitinis_list[1:]:
#     print
#     print(convert_to_cnf([Formula.parse("x"),c]))
# f1 = convert_to_cnf(["kaki", Formula.parse('(x1<->p0)')])
# print(f1)

# print(f1)
# print(c)
# print(f1)
# f1 = list_to_true_cnf(f1)

# model = {"p":True, "q":True, "r":True}
# Tseitinis_list, special_dict = get_Tseitinis_list(phi)
# tseitinis_model(phi,model, special_dict)
# print(model)

# phi = Formula.parse("((p->q)<->~(p->q))")
# Tseitinis_list, special_dict = get_Tseitinis_list(phi)
# f1 = list_to_true_cnf(convert_to_cnf(Tseitinis_list))
# print(is_satisfiable(f1))
# print(compare_formulas(phi, f1, special_dict))

# removal
# f = Formula.parse("(w1|(r|(q|(r|(w1|~w2)))))")
# print(f)
# f_clean = remove_literal_occurs_twice(f)
# print(is_clause_tautlogy(f))
# print(f)

# cnf = [["~r","~w","q11"],["r","p","~w"],["p","q","w"],["w23","w34"]]
# d = dict()
# d["p"]= False
# d["q"] = False
#
# print(BCP(cnf,d))
# print(d)

# c1 = Formula.parse("(~x1|(~x4|x5))") # x4, x5
# c2 = Formula.parse("(~x4|x6)") #x4, x6
# c3 = Formula.parse("(~x5|(~x6|x7))") #x7, x5
# c4 = Formula.parse("(~x7|x8)") #x8 x7
# c5 = Formula.parse("(~x2|(~x7|x9))") #x7, x2
# c6 = Formula.parse("(~x8|~x9)") #x8,x9
# c7 = Formula.parse("(~x8|x9)") #x8,x9
# c8 = Formula.parse("x10") #x8,x9
# l = [c1,c2,c3,c4,c5,c6,c7,c8]
#
# c1 = Formula.parse("(~x1|(~x4|x7))") # x4 , x1
# c2 = Formula.parse("(x4|~x6)") # x4 , x6
# c3 =  Formula.parse("(~x1|~x6)") # x1, x5
# c4 = Formula.parse("x6")
#
# l = [c1,c2,c3,c4]
# f = [Claus(f) for f in l]
#
#
# satsfible, assignmet_map = get_initial_assignment(f)
# print(satsfible, assignmet_map)  #{x6:True}
# watch_literal_map = creates_watch_literals(f)
#
# print("before",watch_literal_map)
# bcp = Bcp(watch_literal_map)
# print(bcp.one_bcp_step(('x6',True)))
# print("after", watch_literal_map)

# # bcp.one_bcp_step(('x2',True))
# # bcp.one_bcp_step(('x3',True))
