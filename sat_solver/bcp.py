import networkx as nx
from typing import *
from parser_util.parser import Literal
from sat_solver.graphs import conflict_analysis
# import matplotlib.pyplot as plt
from smt_solver.smt_helper import *

# constants
PART_A_BCP = False
PART_B_BCP = True


class Bcp:

    def __init__(self, watch_literals, fol_formula=None, substitution_map=None):
        self.current_graph = nx.DiGraph()
        self.current_watch_literals_map = watch_literals
        self.status = []
        self.current_assignment = dict()
        self.current_decision_level = -1
        self.fol_formula = fol_formula
        self.substitution_map = substitution_map
        if not substitution_map is None:
            self.fol_map_to_boolean_map = {substitution_map[k]: k for k in substitution_map}
        else:
            self.fol_map_to_boolean_map = None

    def remove_watch_literal(self, variable, claus):
        if variable in self.current_watch_literals_map.keys():
            if len(self.current_watch_literals_map[variable]) == 1:
                del self.current_watch_literals_map[variable]
            else:
                self.current_watch_literals_map[variable].remove(claus)

    def update_watch_literal_map(self, new_watch_literal, claus, variable):
        self.remove_watch_literal(variable, claus)
        if new_watch_literal not in self.current_watch_literals_map.keys():
            self.current_watch_literals_map[new_watch_literal] = []
        self.current_watch_literals_map[new_watch_literal].append(claus)

    def get_source_and_sink(self, claus, variable):
        sink = list(claus.watch_literals)
        sink.remove(variable)
        sink = sink.pop()
        source = set(claus.variables) - {sink}
        return source, sink

    def add_edges_to_graph(self, source, sink, sink_assignment):
        if sink in self.current_assignment.keys():
            if self.current_assignment[sink] != sink_assignment:
                c = Literal('c', self.current_decision_level, False)
                edges = [(self.get_node_from_graph(s), c) for s in source]
                edges.append((self.get_node_from_graph(sink), c))
                self.current_graph.add_edges_from(edges)
                return
        node = Literal(sink, self.current_decision_level, sink_assignment)
        self.current_graph.add_node(node)
        edges = [(self.get_node_from_graph(s), self.get_node_from_graph(sink)) for s in source if
                 not (self.get_node_from_graph(sink), self.get_node_from_graph(s)) in self.current_graph.edges]
        self.current_graph.add_edges_from(edges)
        return

    def update_graph(self, build_graph_list):
        for source, sink, value in build_graph_list:
            self.add_edges_to_graph(source, sink, value)

    def check_for_one_bcp_assigment(self, variable):
        new_assigments = []
        build_graph_list = []
        # no bcp possible
        if variable not in self.current_watch_literals_map:
            return [], []
        stack = self.current_watch_literals_map[variable].copy()
        for claus in stack:
            claus.update_possible_literals(self.current_assignment.copy())
            # check for wasfull claus
            if not claus.is_satsfied:
                if claus.is_bcp_potential(variable):
                    if claus.all_false(self.current_assignment.copy(), variable):
                        # get the new bcp assignment
                        new_assigment_variable, value = claus.get_bcp_assignment(variable)
                        new_assigments.append((new_assigment_variable, value))
                        # build graph
                        source, sink = self.get_source_and_sink(claus, variable)
                        build_graph_list.append((source, sink, value))

                    vars = claus.watch_literals
                    for var in vars:
                        self.remove_watch_literal(var, claus)
                    # no more watch litrals for this claus / clause is done!
                    claus.is_satsfied = True
                    claus.watch_literals = []
                    claus.possible_watch_literals = []
                else:
                    new_watch_literal = claus.get_new_watch_literal(variable)
                    if new_watch_literal != []:
                        self.update_watch_literal_map(new_watch_literal, claus, variable)
                    else:
                        self.remove_watch_literal(variable, claus)
        return new_assigments, build_graph_list

    def one_bcp_step(self, variable):
        # check for bcp step
        new_assigments, build_graph_list = self.check_for_one_bcp_assigment(variable)
        return new_assigments, build_graph_list

    def update_current_assignment(self, new_assignment):
        for var, assign in new_assignment:
            if var in self.current_assignment.keys():
                if self.current_assignment[var] != assign:
                    return False
            self.current_assignment[var] = assign
        return True

    def intialize_graph(self, new_assignment):
        nodes = []
        for variable, assign in new_assignment:
            self.current_decision_level += 1
            nodes.append(Literal(variable, self.current_decision_level, assign))

        self.current_graph.add_nodes_from(nodes)

    def get_node_from_graph(self, node_name: str):
        for node in self.current_graph.nodes:
            if node.variable_name == node_name:
                return node

    def bcp_step(self, new_assignment: List[Tuple[str, bool]], which_part):
        # if initialzing is non
        if new_assignment == [] and which_part == PART_A_BCP:
            return (1, self.current_assignment)
        self.update_current_assignment(new_assignment)
        stack = [(variable, assign) for variable, assign in new_assignment]
        self.intialize_graph(new_assignment)
        decision = new_assignment[-1][0]
        while stack:
            var, assign = stack.pop()
            # print(f"WATCH LIT:  {self.current_watch_literals_map}")
            add_to_stack, build_graph_list = self.one_bcp_step(var)
            # print(f"?????? {add_to_stack}, {var}")
            stack += add_to_stack
            # todo wrap with boolean flag is smt or not
            if self.fol_map_to_boolean_map:
                if stack == []:
                    # t-propogate, will get boolean assismng and add to "add_to_stack"
                    model_over_formula, filtered_boolean_model = self.convert_boolean_model_to_fol_model()
                    equalities, add_asign = t_propagate(model_over_formula, self.fol_formula)
                    if add_asign != {}:
                        add_to_stack = self.fol_map_to_bool_map_convertor(add_asign)
                        stack += add_to_stack
                        source1 = [self.fol_map_to_boolean_map[k] for k in equalities]
                        self.add_edges_to_graph(source1, add_to_stack[0][0], add_to_stack[0][1])

            # if partial assisngment is t-conflict
            if not (self.update_current_assignment(add_to_stack)):
                if which_part == PART_A_BCP:
                    # unsat because conflict in PART A (the initialzing part)
                    return 0, False
                else:
                    # conflict after decision, do conflict analysis
                    self.update_graph(build_graph_list)
                    c = conflict_analysis(self.current_graph, self.get_node_from_graph(decision),
                                          self.get_node_from_graph("c"))
                    return 2, c
            self.update_graph(build_graph_list)
            # T-CONFLICT
            if not (self.fol_formula is None):  # SMT KICKS IN IFF FOL FORMULA IS DEFINED
                model_over_formula, filtered_boolean_model = self.convert_boolean_model_to_fol_model()
                if model_over_formula != {}:
                    if not (
                            congruence_closure_algorithm(model_over_formula,
                                                         self.fol_formula)):  # THERE IS A T-CONFLICT
                        self.update_graph_with_conflict(filtered_boolean_model)
                        # self.show_graph()
                        if which_part == PART_A_BCP:
                            # unsat because conflict in PART A (the initialzing part)
                            return 0, False
                        else:
                            # conflict after decision, do conflict analysis
                            c = conflict_analysis(self.current_graph, self.get_node_from_graph(decision),
                                                  self.get_node_from_graph("c"))
                            return 2, c
        return 1, self.current_assignment

    # def show_graph(self):
    #     plt.subplot(121)
    #     nx.draw(self.current_graph, with_labels=True, font_weight='bold')
    #     plt.show()

    def convert_assign_map_to_list(self, assign_map):
        return [(k, v) for k, v in assign_map.items()]

    def update_graph_with_conflict(self, assign_map):
        source = [k for k in assign_map.keys()]
        c = Literal('c', self.current_decision_level, False)
        edges = [(self.get_node_from_graph(s), c) for s in source]
        self.current_graph.add_edges_from(edges)
        return

    def convert_boolean_model_to_fol_model(self):
        intersected_keys = list(self.current_assignment.keys() & self.substitution_map.keys())
        model_over_formula_filtered = dict()
        for key in intersected_keys:
            model_over_formula_filtered[key] = self.current_assignment[key]
        return switch_assignment_to_fol_assignment(model_over_formula_filtered,
                                                   self.substitution_map), model_over_formula_filtered

    def fol_map_to_bool_map_convertor(self, sub_map):
        assignment = {self.fol_map_to_boolean_map[k]: v for k, v in
                      sub_map.items()}
        return [(k, v) for k, v in assignment.items()]
