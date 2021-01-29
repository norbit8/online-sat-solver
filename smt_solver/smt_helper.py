from fol.syntax import Formula as fol_Formula
from itertools import product
from fol.syntax import Term

class Node:
    def __init__(self, term):
        self.parent = set()
        self.representative_node = self
        self.term = term

    def __eq__(self, other):
        return self.term == other.term

    # def __str__(self):
    #     return str(self.term)

    def __hash__(self):
        return hash(self.term)


RIGHT_SIDE_EQ = 1

LEFT_SIDE_EQ = 0


def is_unary(s: str) -> bool:
    return s == '~'

def is_binary(s: str) -> bool:
    return s in {'&', '|',  '->', '+', '<->', '-&', '-|'}


def is_function(s: str) -> bool:
    return 'f' <= s[0] <= 't' and s.isalnum()


def is_equality(s: str) -> bool:
    return s == '='


def find_representative(term):
    if term.representative_node != term:
        term.representative_node = find_representative(term.representative_node)
    return term.representative_node



def process_equality(term1, term2):
    term1_representative = find_representative(term1)
    term2_representative = find_representative(term2)

    if len(term1_representative.parent) < len(term2_representative.parent):
        term1_representative, term2_representative = term2_representative, term1_representative
    #term1 is now term2 representative
    term2_representative.representative_node = term1_representative
    #get the product of both term parents
    p = product(term1_representative.parent, term2_representative.parent)
    #union terms parents
    term1_representative.parent = term1_representative.parent | term2_representative.parent
    #term2 has no parents anymore
    term2_representative.parent = set()
    #check parents
    for p1,p2 in p:
        process_equality(p1, p2)


def extract_subterms(term):
    all_subterms = set()
    all_subterms.add(term)
    if is_function(term.root):
        for arg in term.arguments:
            all_subterms = all_subterms | extract_subterms(arg)
    return all_subterms


def get_nodes(equality, dag):
    left_node_eq, right_node_eq = None, None
    for node in dag:
        if node.term == equality.arguments[RIGHT_SIDE_EQ]:
            right_node_eq = node
        elif node.term == equality.arguments[LEFT_SIDE_EQ]:
            left_node_eq = node
        if left_node_eq  and right_node_eq:
            return left_node_eq, right_node_eq



def get_equations(assignment, equality_flag):
    equalities_set = set()
    for equality in assignment:
        if equality_flag:
            if assignment[equality]:
                equalities_set.add(equality)
        else:
            if not assignment[equality]:
                equalities_set.add(equality)
    return equalities_set


def create_dag(all_subterms):
    nodes = dict()
    for term in all_subterms:
        nodes[term] = Node(term)
        if is_function(term.root):
            for arg in term.arguments:
                nodes[arg].parent.add(nodes[term])
    return nodes.values()


def create_subterms_set(formula):
    if is_equality(formula.root):
        return extract_subterms(formula.arguments[LEFT_SIDE_EQ]) | (extract_subterms(formula.arguments[RIGHT_SIDE_EQ]))
    elif is_unary(formula.root):
        return create_subterms_set(formula.first)
    return create_subterms_set(formula.first) | create_subterms_set(formula.second)


def congruence_closure_algorithm(assignment, formula):
    subterms = sorted(list(create_subterms_set(formula)))
    dag = create_dag(subterms)
    inequalities = get_equations(assignment, False)
    equalities = get_equations(assignment, True)
    for equality in equalities:
        left_eq_node, right_eq_node = get_nodes(equality, dag)
        process_equality(left_eq_node, right_eq_node)
    for equality in inequalities:
        left_eq_node, right_eq_node = get_nodes(equality, dag)
        if find_representative(left_eq_node) == find_representative(right_eq_node):
            return False
    return True


def switch_assignment_to_fol_assignment(assignment, map):
    return {map[k]: v for k, v in assignment.items()}

def t_propagate(assignment, formula):
    final_ass = dict()
    subterms = sorted(list(create_subterms_set(formula)))
    dag = create_dag(subterms)
    unassigned_equalities = get_all_equalities_terms(formula)
    equalities = get_equations(assignment, True)
    inequalities = get_equations(assignment, False)
    unassigned_equalities = unassigned_equalities - equalities - inequalities

    for equality in equalities:
        left_eq_node, right_eq_node = get_nodes(equality, dag)
        process_equality(left_eq_node, right_eq_node)
    for equality in unassigned_equalities:
        left, right = get_nodes(equality, dag)
        if find_representative(left) == find_representative(right):
            final_ass[equality] = True
    return equalities,final_ass


def get_all_equalities_terms(formula):
    if is_equality(formula.root):
        return {formula}
    elif is_unary(formula.root):
        return get_all_equalities_terms(formula.first)
    elif is_binary(formula.root):
        return get_all_equalities_terms(formula.first) | get_all_equalities_terms(formula.second)


