from fol.syntax import Formula as fol_Formula
from prop_logic.formula import Formula as PropositionalFormula
from sat_solver.sat_engine import solve_sat
import copy


# todo change impl
def model_over_skeleton_to_model_over_formula(partial_assignment, sub_map):
    assignment = {sub_map[skeleton_var]: skeleton_var_assignment for skeleton_var, skeleton_var_assignment in
                  partial_assignment.items()}
    return assignment


# todo change impl
def get_equalities(assignment):
    equalities = set()
    for equality in assignment:
        if assignment[equality]:
            equalities.add(equality)
    return equalities


# todo change impl
def get_inequalities(assignment):
    equalities = set()
    for equality in assignment:
        if not assignment[equality]:
            equalities.add(equality)
    return equalities


# todo change impl
def get_subterms(formula):
    if is_equality(formula.root):
        return get_subterms_in_term(formula.arguments[0]).union(get_subterms_in_term(formula.arguments[1]))
    elif is_unary(formula.root):
        return get_subterms(formula.first)
    return get_subterms(formula.first) | get_subterms(formula.second)


# todo change impl
def get_subterms_in_term(term):
    subs = {term}
    if is_function(term.root):
        for arg in term.arguments:
            subs.update(get_subterms_in_term(arg))
    return subs


# todo change impl
def make_set(subterms):
    nodes = dict()
    for term in subterms:
        nodes[term] = Node(term)
        if is_function(term.root):
            for arg in term.arguments:
                nodes[arg].parent = nodes[term]
    return nodes.values()


# todo change impl
def find(term):
    if term.represent != term:
        term.represent = find(term.represent)
    return term.represent


# todo change impl
def union(term1, term2):
    x_rep = find(term1)
    y_rep = find(term2)

    if x_rep == y_rep:
        pass
    if x_rep.size < y_rep.size:
        x_rep, y_rep = y_rep, x_rep
    y_rep.represent = x_rep
    x_rep.size = x_rep.size + y_rep.size
    # todo change to for loop because lecture 8 p25
    if term1.parent != term1 or term2.parent != term2:
        union(term1.parent, term2.parent)


# todo change impl
def get_nodes(equality, disjoint_set):
    node1, node2 = None, None
    for node in disjoint_set:
        if node.term == equality.arguments[0]:
            node1 = node
        elif node.term == equality.arguments[1]:
            node2 = node
        if node1 is not None and node2 is not None:
            break
    return node1, node2


# todo change impl
def check_congruence_closure(assignment, formula):
    subterms = sorted(list(get_subterms(formula)))
    disjoint_set = make_set(subterms)
    equalities = get_equalities(assignment)
    inequalities = get_inequalities(assignment)
    for equality in equalities:
        node1, node2 = get_nodes(equality, disjoint_set)
        union(node1, node2)
    for equality in inequalities:
        node1, node2 = get_nodes(equality, disjoint_set)
        if find(node1) == find(node2):
            return False
    return True


# todo change impl
def get_conflict(assignment):
    formula = '('
    num_vars = len(assignment.keys())
    i = 1
    for a, v in assignment.items():
        if v:
            formula += '~' + str(a)
        else:
            formula += str(a)
        if i == num_vars:
            formula += ')' * (num_vars - 1)
        else:
            formula += '|'
            if i < num_vars - 1:
                formula += '('
        i += 1
    return PropositionalFormula.parse(formula)


def is_equality(s: str) -> bool:
    return s == '='


def is_unary(s: str) -> bool:
    return s == '~'


def is_function(s: str) -> bool:
    return 'f' <= s[0] <= 't' and s.isalnum()


def smt_solver(original_formula: str):
    return solve_sat(original_formula, smt_flag=True)


