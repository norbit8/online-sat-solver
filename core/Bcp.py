import networkx as nx
from typing import *
from Parser import Literal
from Graphs import conflict_analysis
import matplotlib.pyplot as plt

# constants
PART_A_BCP = False
PART_B_BCP = True


class Bcp:

    def __init__(self, watch_literals):
        self.current_graph = nx.DiGraph()
        self.current_watch_literals_map = watch_literals
        self.status = []
        self.current_assignment = dict()
        self.current_decision_level = -1

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
        edges = [(self.get_node_from_graph(s), self.get_node_from_graph(sink)) for s in source]
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
        print("finish inner loop")
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
            print("bcp loop")

            var, assign = stack.pop()
            # print(f"WATCH LIT:  {self.current_watch_literals_map}")
            add_to_stack, build_graph_list = self.one_bcp_step(var)
            # print(f"?????? {add_to_stack}, {var}")
            stack += add_to_stack
            # cehcks for conflict
            if not (self.update_current_assignment(add_to_stack)):
                if which_part == PART_A_BCP:
                    # unsat because conflict in PART A (the initialzing part)
                    return (0, False)
                else:
                    # conflict after decision, doint conflict analasis
                    self.update_graph(build_graph_list)
                    print("START")
                    c = conflict_analysis(self.current_graph, self.get_node_from_graph(decision),
                                          self.get_node_from_graph("c"))
                    # print("here is conflict!",c, type(c))
                    return (2, c)
            print("STOP")
            self.update_graph(build_graph_list)
        # bcp ok, no conflicts
        return 1, self.current_assignment

    def show_graph(self):
        # print(self.current_graph.edges)
        for node in self.current_graph.nodes:
            print(node.variable_name, node.decision_level)
        plt.subplot(121)
        nx.draw(self.current_graph, with_labels=True, font_weight='bold')
        plt.show()
