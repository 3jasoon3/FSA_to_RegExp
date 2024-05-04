import re
from collections import defaultdict
from typing import List

"""reg_exp_converter.py: Converts (N)FSA into a regular expression."""
__author__      = "Egor Chernobrovkin, Innopolis University"

class Node:
    def __init__(self, label: str = "") -> None:
        self.label: str = label
        self.adjacent_nodes: List[Node] = []
        self.is_visited: bool = False
    
    def addEdge(self, adjacent_node) -> None:
        if adjacent_node.getLabel() not in [node.getLabel() for node in self.adjacent_nodes]:
            self.adjacent_nodes.append(adjacent_node)

    def setVisited(self, is_visited: bool = True) -> None:
        self.is_visited = is_visited

    def isVisited(self) -> bool:
        return self.is_visited
    
    def getAdjacentNodes(self) -> List:
        return self.adjacent_nodes
    
    def getLabel(self) -> str:
        return self.label


class Graph:
    def __init__(self, number_of_states: int) -> None:
        self.number_of_states: int = number_of_states
        self.node_list: List[Node] = []

    def __depthFirstSearch(self, node: Node, new_nodes: list) -> None:
        new_nodes.append(node)
        node.setVisited()
        adjacentNodes = node.getAdjacentNodes()
        for adjacentNode in adjacentNodes:
            if not adjacentNode.isVisited():
                self.__depthFirstSearch(adjacentNode, new_nodes)
    
    def addNode(self, label: str) -> Node:
        if label not in [node.getLabel() for node in self.node_list]:
            node = Node(label)
            self.node_list.append(node)
            return node
        else:
            for node in self.node_list:
                if node.getLabel() == label: 
                    return node
    
    def addEdge(self, s_node: Node, d_node: Node) -> None:
        s_node.addEdge(d_node)
    
    def isRegular(self, init_node: Node) -> bool:
        new_nodes: list[Node] = []
        self.__depthFirstSearch(init_node, new_nodes)
        if len(new_nodes) == self.number_of_states: return True
        return False
    

class ConverterException(Exception):
    def __init__(self, message: str) -> None:
        super().__init__(self)
        self.message = message

    def __str__(self) -> str:
        return self.message


class InputIsMalformedException(ConverterException):
    def __init__(self) -> None:
        self.message = "E1: Input file is malformed"


class InitStateIsNotDefinedException(ConverterException):
    def __init__(self) -> None:
        self.message = "E2: Initial state is not defined"


class NoAcceptingStatesException(ConverterException):
    def __init__(self) -> None:
        self.message = "E3: Set of accepting states is empty"


class InvalidStateException(ConverterException):
    def __init__(self, state: str) -> None:
        self.message = f"E4: A state '{state}' is not in the set of states"


class InvalidTransitionException(ConverterException):
    def __init__(self, transition: str) -> None:
        self.message = f"E5: A transition '{transition}' is not represented in the alphabet"


class DisjointStatesException(ConverterException):
    def __init__(self) -> None:
        self.message = "E6: Some states are disjoint"


class InvalidFSATypeException(ConverterException):
    def __init__(self) -> None:
        self.message = "E7: FSA is non-deterministic"


class RegularExpressionConverter:
    def __init__(self, input_path: str) -> None:
        self.input_path: str = input_path
        self.automaton_type: str = None
        self.states: List = []
        self.alphabet: List = []
        self.initial_state: str = ""
        self.accepting_states: list = []
        self.transitions: List = []
        self.validation_result: bool = True
        self.epsilon: str = "eps"
        self.empty_set: str = "{}"

    def __extract(self) -> None:
        parsed_vals: List[str] = []
        commands: List[str] = ["type", "states", "alphabet",
                               "initial", "accepting", "transitions"]
        try:
            with open(self.input_path, 'r') as file:
                for i, line in enumerate(file):
                    if commands[i] not in line: raise InputIsMalformedException
                    parsed_value = re.findall(r'\[([^\]]+)\]', line)
                    parsed_vals.append(parsed_value)
            self.automaton_type = parsed_vals[0][0]
            self.states = list(set(parsed_vals[1][0].split(',')))
            self.states.sort()
            self.alphabet = parsed_vals[2][0].split(',')
            self.initial_state = parsed_vals[3][0]
            self.accepting_states = parsed_vals[4][0].split(',')
            self.transitions = parsed_vals[5][0].split(',')
        except:
            raise InputIsMalformedException

    def __validate(self) -> None:
        # Error 1: Input file is malformed
        if len(self.transitions) != len(set(self.transitions)): raise InputIsMalformedException

        # Error 2: Initial state is not defined
        if not self.initial_state:
            raise InitStateIsNotDefinedException
        if self.initial_state not in self.states: raise InvalidStateException(self.initial_state)
        
        # Error 3: Set of accepting states is empty
        if not self.accepting_states:
            raise NoAcceptingStatesException
        
        # Error 4, 5: A state/transition is not in the set of states/alphabet
        for state in self.accepting_states:
            if state not in self.states: raise InvalidStateException(state)
        for transition in self.transitions:
            s_state, s_transition, d_state = transition.split('>')
            if not s_state: raise InputIsMalformedException
            if s_state not in self.states: raise InvalidStateException(s_state)
            if d_state not in self.states: raise InvalidStateException(d_state)
            if s_transition not in self.alphabet: raise InvalidTransitionException(s_transition)
        
        # Error 6: Some states are disjoint
        graph = Graph(len(self.states))
        init_node = Node()
        for transition in self.transitions:
            s_state, s_transition, d_state = transition.split('>')
            s_node = graph.addNode(s_state)
            d_node = graph.addNode(d_state)
            graph.addEdge(s_node, d_node)
            if s_node.getLabel() == self.initial_state: init_node = s_node
            if d_node.getLabel() == self.initial_state: init_node = d_node
        if not graph.isRegular(init_node): raise DisjointStatesException
        
        # Error 7: FSA is non-deterministic
        if self.automaton_type == "deterministic":
            state_transitions = defaultdict(list)
            for transition in self.transitions:
                s_state, s_transition, d_state = transition.split('>')
                state_transitions[s_state].append(s_transition)
            for transitions in state_transitions.values():
                if len(set(transitions)) != len(transitions):
                    raise InvalidFSATypeException
            
    def __buildInitialRegExp(self) -> List[List]:
        initial_regular_expression: List = [['' for row in range(len(self.states))]
                                            for column in range(len(self.states))]
        for i, i_state in enumerate(self.states):
            for j, j_state in enumerate(self.states):
                new_regular_expression = ""
                for transition in self.transitions:
                    s_state, s_transition, d_state = transition.split('>')
                    if (s_state, d_state) == (i_state, j_state): new_regular_expression += f"{s_transition}|"
                if i_state == j_state: new_regular_expression += self.epsilon
                if not new_regular_expression: new_regular_expression = self.empty_set
                new_regular_expression = new_regular_expression[:-1] if '|' in new_regular_expression[-1] else new_regular_expression
                initial_regular_expression[i][j] = new_regular_expression
        return initial_regular_expression

    def convert(self) -> str:
        try:
            self.__extract()
            self.__validate()
        except ConverterException as exception:
            print(exception)
            exit()
        initial_regular_expression = self.__buildInitialRegExp()
        for step in range(len(self.states)):
            regular_expression = [[0 for row in range(len(self.states))]
                                  for column in range(len(self.states))]
            for i in range(len(self.states)):
                for j in range(len(self.states)):
                    regular_expression[i][j] = f"({initial_regular_expression[i][step]})({initial_regular_expression[step][step]})*({initial_regular_expression[step][j]})|({initial_regular_expression[i][j]})"
            initial_regular_expression = regular_expression
        
        answer: str = ""
        path: int = 0

        for i in range(len(self.states)):
            if self.states[i] in self.accepting_states:
                path += 1
                answer += f"({initial_regular_expression[0][i]})|"

        match path:
            case 0:
                return self.empty_set
            case _:
                return f"{answer[:-1]}"

def main():
    input_path = r"input.txt"
    converter = RegularExpressionConverter(input_path)
    answer = converter.convert()
    print(answer)

if __name__ == "__main__":
    main()