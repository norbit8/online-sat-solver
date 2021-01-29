from __future__ import annotations
from parser_util.parser import Literal
from prop_logic.formula import Formula
from typing import List
from parser_util.parser import Claus
import networkx as nx
import matplotlib.pyplot as plt


def find_uip(g, current_decision_node):
    """
    Given a graph finds its uip.
    :param g: graph.
    :param current_decision_node: current decision node.
    :return: the uip.
    """
    s = {current_decision_node}
    uid = {current_decision_node}
    while len(s) != 0:
        s_temp = set()
        for node in s:
            for n in list(g.successors(node)):
                s_temp.add(n)
        s = s_temp
        if len(s) == 1 and list(g.successors(list(s)[0])) != []:
            uid = s
        # print("NO CYCLE: ", [cycle for cycle in nx.simple_cycles(g)])
        # show_graph(g)
    return uid.pop()


def last_assigned_literal(g, list_of_literals, first_uip_dont_take):
    """
    Given a graph and a node gets the last assigned literal.
    :param g: Conflict graph.
    :param node: Current node to look for the last assigned literal from his clause
    :return:
    """
    if list_of_literals[0] == first_uip_dont_take:
        current_last_ass_literal = list_of_literals[1]
    else:
        current_last_ass_literal = list_of_literals[0]
    if len(list_of_literals) == 0:
        print("Something went wrong, the list of literals is empty!")
        return
    for lit in list_of_literals[1:]:
        if lit.decision_level > current_last_ass_literal.decision_level and lit != first_uip_dont_take:
            current_last_ass_literal = lit
    return current_last_ass_literal


def get_clause(g, node, is_conflict=False):
    """
    Given a graph and a node, gets the nodes clause.
    :param g: Graph.
    :param node: Node.
    :param is_conflict:
    :return:
    """
    if is_conflict:
        fake_clause = []
    else:
        fake_clause = [Literal(node.variable_name, node.decision_level, not (node.assignment))]
    list_of_literals = list(g.predecessors(node))
    for lit in list_of_literals:
        new_lit = Literal(lit.variable_name, lit.decision_level, not (lit.assignment))
        fake_clause.append(new_lit)
    return fake_clause


def check_if_should_stop(current_clause, first_uip):
    """
    This is the condition if I should stop the search for the conflict clause
    :param current_clause:
    :param first_uip:
    :return:
    """
    # print(create_clause(current_clause), first_uip.variable_name)
    if first_uip in current_clause:
        for lit in current_clause:
            if lit != first_uip and lit.decision_level == first_uip.decision_level:
                return True  # continue iteration
        # if current_clause[current_clause.index(first_uip)].assignment == False:
        return False
    return True


def resolve_clause(c1, c2):
    """
    Resolving a fake clause (List of literals)
    :param c1: List of literals 1
    :param c2: List of literals 2
    :return: List of literals 3.
    """
    resolvent = set()
    for lit1 in c1:
        if lit1 in c2:
            idx = c2.index(lit1)
            if c2[idx].assignment == lit1.assignment:
                resolvent.add(lit1)
        else:
            resolvent.add(lit1)
    for lit2 in c2:
        if lit2 in c1:
            idx = c1.index(lit2)
            if c1[idx].assignment == lit2.assignment:
                resolvent.add(lit2)
        else:
            resolvent.add(lit2)
    return list(resolvent)


def create_clause(fake_clause: List[Literal]):
    """
    This function creates a clause out of a list of literals
    :param fake_clause: List of literals
    :return: A clause
    """
    formula = ""
    list_of_vars = []
    for lit in fake_clause:
        if not lit.assignment:
            list_of_vars.append("~" + lit.variable_name)
        else:
            list_of_vars.append(lit.variable_name)
    if len(list_of_vars) == 1:
        return Claus(Formula.parse(list_of_vars[0]))
    for index, item in enumerate(list_of_vars):
        if index == len(list_of_vars) - 1:
            formula += item
        else:
            formula += "(" + item + "|"
    formula += ")" * (len(list_of_vars) - 1)
    return Claus(Formula.parse(formula))


def get_conflict(g, conflict_node):
    s = {conflict_node}
    result = set()
    while len(s) != 0:
        working_node = s.pop()
        if list(g.predecessors(working_node)) == []:
            result.add(working_node)
        else:
            for predecessor in list(g.predecessors(working_node)):
                s.add(predecessor)
    fake_clause = []
    for item in list(result):
        fake_clause.append(Literal(item.variable_name, item.decision_level, not (item.assignment)))
    return create_clause(fake_clause)


def conflict_analysis(g, current_decision_node, conflict_node):
    """
    Conflict analysis mode implementation
    :param g: Conflict graph.
    :param current_decision_node: The current decision node.
    :param conflict_node: The conflict node.
    :return: The conflict clause.
    """
    first_uip = find_uip(g, current_decision_node)
    current_clause = get_clause(g, conflict_node, True)
    counter = 0
    while check_if_should_stop(current_clause, first_uip):
        # counter += 1
        # if counter > len(g.nodes):
        #     return False
        # print("Conflict clause: ", create_clause(current_clause))
        if current_clause == []:
            return get_conflict(g, conflict_node)
        lal = last_assigned_literal(g, current_clause, first_uip)
        # print("Last assigned literal in conflict: ", create_clause([lal]))
        clause = get_clause(g, lal, False)
        # print("Clause is:", create_clause(clause))
        current_clause = resolve_clause(current_clause, clause)
    return create_clause(current_clause)


def show_graph(g):
    # print(self.current_graph.edges)
    # for node in g.nodes:
    #     print(node.variable_name, node.decision_level)
    plt.subplot(121)
    nx.draw(g, with_labels=True, font_weight='bold')
    plt.show()

# DG = nx.DiGraph()
# DG.add_nodes_from([1, 2, 3, 4, 5, 6, 7, 8, 9, 10])
# DG.add_edges_from([(7, 5), (7, 6), (8, 6), (6, 4), (5, 4), (4, 3), (4, 'c'), (3, 'c'), (2, 'c'), (1, 2)])
# print(find_uip(DG, 7))
# conflict_analysis(DG, 7, 'c')

# Lecture 3 - slide 30 example UIPs and Resolution
# graph = nx.DiGraph()
# x8 = Literal('x8', 4, True)
# x7 = Literal('x7', 8, False)
# x6 = Literal('x6', 8, False)
# x5 = Literal('x5', 8, False)
# x4 = Literal('x4', 8, True)
# x3 = Literal('x3', 8, False)
# x2 = Literal('x2', 1, False)
# x1 = Literal('x1', 1, True)
# c = Literal('c', 8, True)
# graph.add_nodes_from([x1, x2, x3, x4, x5, x6, x7, x8, c])
# graph.add_edges_from([(x8, x6), (x7, x6), (x7, x5), (x5, x4), (x6, x4), (x4, x3), (x3, c), (x4, c), (x2, c), (x1, x2)])
# print(conflict_analysis(graph, x7, c))
# ------------------------------------------------
# Lecture 3 - slide 33 example UIPs and Resolution
# graph2 = nx.DiGraph()
# x2 = Literal('x2', 4, False)
# x4 = Literal('x4', 5, True)
# x9 = Literal('x9', 4, False)
# x5 = Literal('x5', 5, False)
# x6 = Literal('x6', 5, True)
# x7 = Literal('x7', 5, False)
# c = Literal('c', 5, True)
# graph2.add_nodes_from([x2, x4, x5, x6, x7, x9, c])
# graph2.add_edges_from([(x2, x5), (x4, x5), (x4, x6), (x9, x6), (x5, x7), (x6, x7), (x6, c), (x7, c)])
# print(type(get_node_from_graph(graph2, 'x2')))
# print(conflict_analysis(graph2, x4, c))
# ------------------------------------------------
# Slide 40
# graph2 = nx.DiGraph()
# x1 = Literal('x1', 1, True)
# x4 = Literal('x4', 4, True)
# x3 = Literal('x3', 3, True)
# x5 = Literal('x5', 4, True)
# x6 = Literal('x6', 4, True)
# x7 = Literal('x7', 4, True)
# x8 = Literal('x8', 4, True)
# x9 = Literal('x9', 4, True)
# x2 = Literal('x2', 2, True)
# c = Literal('c', 5, True)
# graph2.add_nodes_from([x1, x2, x3, x4, x5, x6, x7, x8, x9, c])
# graph2.add_edges_from(
#     [(x1, x5), (x4, x5), (x4, x6), (x5, x7), (x6, x7), (x7, x8), (x7, x9), (x9, c), (x8, c), (x2, x9)])
# # print(type(get_node_from_graph(graph2, 'x2')))
# print(conflict_analysis(graph2, x4, c))


# print(x1 in [x3, x4])
# print(create_clause([x3]))
# gr.add_nodes_from([x1, x2])
# gr.add_edges_from([(x1, x2)])
# print("HO", list(gr.successors(x1))[0].decision_level)

# DG = nx.DiGraph()
# DG.add_nodes_from([1,2,3,4,5,6,7,8,'c'])
# DG.add_edges_from([(8,6),(7,5),(5,4),(6,4),(4,3),(4,'c'),(3,'c'),(2,'c'),(1,2)])
# find_uip(DG, 7)

# DG = nx.DiGraph()
# DG.add_nodes_from([1,2,3,4,5,6,7,8,9,10])
# from Solver import Claus
# from Formula import Formula
# DG.add_edge(1, 2, weight=Claus(Formula("q")))
# c = DG.edges[1,2]['weight']
# print(c)
