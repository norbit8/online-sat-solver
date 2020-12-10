from __future__ import annotations
from typing import Mapping, Optional, Set, Tuple, Union, List
import itertools
from functools import reduce

EMPTY_STRING = "Empty string"

INVALID_LETTER = "Invalid letter"

MISSING_OPERATOR = "Missing Operator"

MISSING_PARENT = "Missing ')'"

UNEXPECTED_SYMBOL = "Unexpected symbol"



def is_variable(s: str) -> bool:
    """Checks if the given string is an atomic proposition.
    Parameters:
        s: string to check.
    Returns:
        ``True`` if the given string is an atomic proposition, ``False``
        otherwise.
    """
    if (is_unary(s) or is_binary(s)):
        return False
    return s[0] >= 'p' and s[0] <= 'z' and (len(s) == 1 or s[1:].isdigit())


def is_constant(s: str) -> bool:
    """Checks if the given string is a constant.
    Parameters:
        s: string to check.
    Returns:
        ``True`` if the given string is a constant, ``False`` otherwise.
    """
    return s == 'T' or s == 'F'


def is_base_formula(f):
    if is_unary(f.root):
        return is_variable(f.first.root)
    elif is_binary(f.root):
        if is_unary(f.first.root):
            return is_variable(f.first.first.root) and is_variable(f.second.root)
        elif is_unary(f.second.root):
            return  is_variable(f.first.root) and is_unary(f.second.root) and is_variable(f.second.first.root)
        else:
            return (is_variable(f.first.root) and is_variable(f.second.root))


def is_unary(s: str) -> bool:
    """Checks if the given string is a unary operator.
    Parameters:
        s: string to check.
    Returns:
        ``True`` if the given string is a unary operator, ``False`` otherwise.
    """
    return s == '~'

def is_binary(s: str) -> bool:
    """Checks if the given string is a binary operator.
    Parameters:
        s: string to check.
    Returns:
        ``True`` if the given string is a binary operator, ``False`` otherwise.
    """
    #return s == '&' or s == '|' or s == '->'
    # For Chapter 3:
    return s in {'&', '|',  '->', '+', '<->', '-&', '-|'}


def obtain_variable(s: str) -> Tuple[Union[Formula, None], str]:
    var = ""
    rest = ""
    for index in range(len(s)):
        var += s[index]
        if not (is_variable(var)):
            rest = s[index:]
            var = var[:-1]
            break
    return Formula(var), rest


def obtain_formula_unaries(s: str) -> Tuple[Union[Formula, None], str]:
    rest = Formula.parse_prefix(s[1:])
    if (rest[0] is None):
        return None, ""
    formul = Formula(s[0], rest[0])
    rest = rest[1]
    return formul, rest


def formula_is_single_char(s: str) -> Tuple[Union[Formula, None], str]:
    if is_variable(s) or is_constant(s):
        return Formula(s), ""
    else:
        return None, ""


def open_parentheses(s: str) -> Tuple[Union[Formula, None], str]:
    pp = Formula.parse_prefix(s[1:])
    var = pp[0]
    if var is None:
        return None, ""
    if (not is_binary(pp[1][0])) and (not is_binary(pp[1][:2])) and (not is_binary(pp[1][:3])):
        return None, MISSING_OPERATOR
    else:
        st = ""
        op = ""
        # NaNd nor and if
        if pp[1][0] == '-':
            st = pp[1][2:]
            op = pp[1][:2]
        # iff
        elif pp[1][0] == '<':
            st = pp[1][3:]
            op = pp[1][:3]
        else:
            st = pp[1][1:]
            op = pp[1][0]
        pp2 = Formula.parse_prefix(st)
        if pp2[1] == "" or pp2[1][0] != ')':
            return None, MISSING_PARENT
        else:
            var = Formula(op, var, pp2[0])
            return var, pp2[1][1:]


def sub_op(res, p, substitution_map, rest):
    if str(p) == "q":
        res = res.substitute_variables({"p": Formula.parse(str(p) + "1")})  # left
        res = res.substitute_variables(
            {"q": Formula.parse_prefix(rest)[0].substitute_operators(substitution_map)})  # right
        res = res.substitute_variables({str(p) + "1": p})  # left
    else:
        res = res.substitute_variables({"p": p})  # left
        res = res.substitute_variables(
            {"q": Formula.parse_prefix(rest)[0].substitute_operators(substitution_map)})  # right
    return str(res)


class Formula:
    """An immutable propositional formula in tree representation.
    Attributes:
        root (`str`): the constant, atomic proposition, or operator at the root
            of the formula tree.
        first (`~typing.Optional`\\[`Formula`]): the first operand to the root,
            if the root is a unary or binary operator.
        second (`~typing.Optional`\\[`Formula`]): the second operand to the
            root, if the root is a binary operator.
    """
    id : int
    root: str
    first: Optional[Formula]
    second: Optional[Formula]

    count = 0

    @classmethod
    def incr(self):
        self.count += 1
        return self.count

    def __init__(self, root: str, first: Optional[Formula] = None,
                 second: Optional[Formula] = None) -> None:
        """Initializes a `Formula` from its root and root operands.
        Parameters:
            root: the root for the formula tree.
            first: the first operand to the root, if the root is a unary or
                binary operator.
            second: the second operand to the root, if the root is a binary
                operator.
        """
        self.id = self.incr()
        if is_variable(root) or is_constant(root):
            assert first is None and second is None
            self.root = root
        elif is_unary(root):
            assert type(first) is Formula and second is None
            self.root, self.first = root, first
        else:
            assert is_binary(root) and type(first) is Formula and \
                   type(second) is Formula
            self.root, self.first, self.second = root, first, second

    def __eq__(self, other: object) -> bool:
        """Compares the current formula with the given one.
        Parameters:
            other: object to compare to.
        Returns:
            ``True`` if the given object is a `Formula` object that equals the
            current formula, ``False`` otherwise.
        """
        return isinstance(other, Formula) and str(self) == str(other)

    def __ne__(self, other: object) -> bool:
        """Compares the current formula with the given one.
        Parameters:
            other: object to compare to.
        Returns:
            ``True`` if the given object is not a `Formula` object or does not
            does not equal the current formula, ``False`` otherwise.
        """
        return not self == other

    def __hash__(self) -> int:
        return hash(str(self))

    def __repr__(self) -> str:
        """Computes the string representation of the current formula.
        Returns:
            The standard string representation of the current formula.
        """
        # Task 1.1
        formulaStrRep = self.root
        if hasattr(self, "first") and hasattr(self, "second"):
            formulaStrRep = "(" + str(self.first) + formulaStrRep + str(self.second) + ")"
        if hasattr(self, "first") and not hasattr(self, "second"):
            formulaStrRep = formulaStrRep + str(self.first)
        return formulaStrRep

    def variables(self) -> Set[str]:
        """Finds all atomic propositions (variables) in the current formula.
        Returns:
            A set of all atomic propositions used in the current formula.
        """
        # Task 1.2
        vars = set()
        if is_variable(self.root):
            vars.add(self.root)
        if hasattr(self, "first"):
            vars = vars.union(self.first.variables())
        if hasattr(self, "second"):
            vars = vars.union(self.second.variables())
        return vars

    def variables_list(self) -> Set[str]:
        """Finds all atomic propositions (variables) in the current formula.
        Returns:
            A set of all atomic propositions used in the current formula.
        """
        # Task 1.2
        vars = list()
        if is_variable(self.root):
            vars.append(self.root)
        if hasattr(self, "first"):
            vars.append(self.first.variables())
        if hasattr(self, "second"):
           vars.append(self.second.variables())
        single_list = reduce(lambda x, y: list(x) + list(y), vars)
        return single_list

    def operators(self) -> Set[str]:
        """Finds all operators in the current formula.
        Returns:
            A set of all operators (including ``'T'`` and ``'F'``) used in the
            current formula.
        """
        # Task 1.3
        vars = set()
        if is_binary(self.root) or is_unary(self.root) or is_constant(self.root):
            vars.add(self.root)
        if hasattr(self, "first"):
            vars = vars.union(self.first.operators())
        if hasattr(self, "second"):
            vars = vars.union(self.second.operators())
        return vars

    @staticmethod
    def parse_prefix(s: str) -> Tuple[Union[Formula, None], str]:
        """Parses a prefix of the given string into a formula.
        Parameters:
            s: string to parse.
        Returns:
            A pair of the parsed formula and the unparsed suffix of the string.
            If the first token of the string is a variable name (e.g.,
            ``'x12'``), then the parsed prefix will be that entire variable name
            (and not just a part of it, such as ``'x1'``). If no prefix of the
            given string is a valid standard string representation of a formula
            then returned pair should be of ``None`` and an error message, where
            the error message is a string with some human-readable content.
        """
        # Task 1.4
        if s == "":
            return None, EMPTY_STRING

        if len(s) == 1:
            return formula_is_single_char(s)

        else:
            # String begins with an open parentheses
            if s[0] == "(":
                return open_parentheses(s)

            # String begins with a constant
            if is_constant(s[0]):
                return Formula(s[0]), s[1:]

            # String begins with a variable
            if is_variable(s[0]):
                return obtain_variable(s)

            # String begins with unary
            if is_unary(s[0]):
                return obtain_formula_unaries(s)

            return None, UNEXPECTED_SYMBOL

    @staticmethod
    def is_formula(s: str) -> bool:
        """Checks if the given string is a valid representation of a formula.
        Parameters:
            s: string to check.
        Returns:
            ``True`` if the given string is a valid standard string
            representation of a formula, ``False`` otherwise.
        """
        # Task 1.5
        if Formula.parse_prefix(s)[0] is None:
            return False
        if Formula.parse_prefix(s)[1] != "":
            return False
        return True


    @staticmethod
    def parse(s: str) -> Formula:
        """Parses the given valid string representation into a formula.
        Parameters:
            s: string to parse.
        Returns:
            A formula whose standard string representation is the given string.
        """
        assert Formula.is_formula(s)
        # Task 1.6
        return Formula.parse_prefix(s)[0]

# Optional tasks for Chapter 1

    def polish(self) -> str:
        """Computes the polish notation representation of the current formula.
        Returns:
            The polish notation representation of the current formula.
        """
        # Optional Task 1.7

    @staticmethod
    def parse_polish(s: str) -> Formula:
        """Parses the given polish notation representation into a formula.
        Parameters:
            s: string to parse.
        Returns:
            A formula whose polish notation representation is the given string.
        """
        # Optional Task 1.8

# Tasks for Chapter 3

    def substitute_variables(self, substitution_map: Mapping[str, Formula]) -> Formula:
        """Substitutes in the current formula, each variable `v` that is a key
        in `substitution_map` with the formula `substitution_map[v]`.
        Parameters:
            substitution_map: the mapping defining the substitutions to be
                performed.
        Returns:
            The resulting formula.
        Examples:
            >>> Formula.parse('((p->p)|z)').substitute_variables(
            ...     {'p': Formula.parse('(q&r)')})
            (((q&r)->(q&r))|z)
        """
        for variable in substitution_map:
            assert is_variable(variable)
        # Task 3.3
        f = str(self)
        if is_variable(Formula.parse(f).root) and Formula.parse(f).root in substitution_map:
            f = str(substitution_map[Formula.parse(f).root])
        elif is_unary(Formula.parse(f).root):
            first = str(Formula.parse(f).first.substitute_variables(substitution_map))
            f = Formula.parse(f).root + first
        elif is_binary(Formula.parse(f).root):
            first = str(Formula.parse(f).first.substitute_variables(substitution_map))
            second = str(Formula.parse(f).second.substitute_variables(substitution_map))
            f = "(" + first + Formula.parse(f).root + second + ")"
        return Formula.parse(f)

    def substitute_operators(
            self, substitution_map: Mapping[str, Formula]) -> Formula:
        """Substitutes in the current formula, each constant or operator `op`
        that is a key in `substitution_map` with the formula
        `substitution_map[op]` applied to its (zero or one or two) operands,
        where the first operand is used for every occurrence of ``'p'`` in the
        formula and the second for every occurrence of ``'q'``.
        Parameters:
            substitution_map: the mapping defining the substitutions to be
                performed.
        Returns:
            The resulting formula.
        Examples:
            >>> Formula.parse('((x&y)&~z)').substitute_operators(
            ...     {'&': Formula.parse('~(~p|~q)')})
            ~(~~(~x|~y)|~~z)
        """
        for operator in substitution_map:
            assert is_binary(operator) or is_unary(operator) or \
                   is_constant(operator)
            assert substitution_map[operator].variables().issubset({'p', 'q'})
        # Task 3.4
        old = str(self)
        if old[0] == "~":
            if "~" in substitution_map:
                ret = Formula.parse(old[1:]).substitute_operators(substitution_map)
                return substitution_map["~"].substitute_variables({"p": ret})
            else:
                return Formula.parse("~" + str(Formula.parse(old[1:]).substitute_operators(substitution_map)))
        if "T" in substitution_map and "T" in old:
            old = old.replace("T", str(substitution_map["T"]))
        if "F" in substitution_map and "F" in old:
            old = old.replace("F", str(substitution_map["F"]))
        if old[0] == "(":
            tup = Formula.parse_prefix(old[1:])
            rest, p = (tup[1], tup[0].substitute_operators(substitution_map))
            if rest[0:2] == "-|":
                if "-|" in substitution_map:
                    old = sub_op(substitution_map["-|"], p, substitution_map, rest[2:])
                else:
                    old = "(" + str(p) + "-|" + str(
                        Formula.parse_prefix(rest[2:])[0].substitute_operators(substitution_map)) + \
                          Formula.parse_prefix(rest[2:])[1]
            if rest[0:2] == "-&":
                if "-&" in substitution_map:
                    old = sub_op(substitution_map["-&"], p, substitution_map, rest[2:])
                else:
                    old = "(" + str(p) + "-&" + str(Formula.parse_prefix(rest[2:])[0].substitute_operators(substitution_map))\
                          + Formula.parse_prefix(rest[2:])[1]
            if rest[0:2] == "->":
                if "->" in substitution_map:
                    old = sub_op(substitution_map["->"], p, substitution_map, rest[2:])
                else:
                    old = "(" + str(p) + "->" + str(Formula.parse_prefix(rest[2:])[0].substitute_operators(substitution_map))\
                          + Formula.parse_prefix(rest[2:])[1]
            if rest[0] == "+":
                if "+" in substitution_map:
                    old = sub_op(substitution_map["+"], p, substitution_map, rest[1:])
                else:
                    old = "(" + str(p) + "+" + str(Formula.parse_prefix(rest[1:])[0].substitute_operators(substitution_map))\
                          + Formula.parse_prefix(rest[1:])[1]
            if rest[0:3] == "<->":
                if "<->" in substitution_map:
                    old = sub_op(substitution_map["<->"], p, substitution_map, rest[3:])
                else:
                    old = "(" + str(p) + "<->" + str(Formula.parse_prefix(rest[3:])[0].substitute_operators(substitution_map))\
                          + Formula.parse_prefix(rest[3:])[1]
            if rest[0] == "&":
                if "&" in substitution_map:
                    old = sub_op(substitution_map["&"], p, substitution_map, rest[1:])
                else:
                    old = "(" + str(p) + "&" + str(Formula.parse_prefix(rest[1:])[0].substitute_operators(substitution_map))\
                          + Formula.parse_prefix(rest[1:])[1]
            if rest[0] == "|":
                if "|" in substitution_map:
                    old = sub_op(substitution_map["|"], p, substitution_map, rest[1:])
                else:
                    old = "(" + str(p) + "|" + str(Formula.parse_prefix(rest[1:])[0].substitute_operators(substitution_map))\
                          + Formula.parse_prefix(rest[1:])[1]
        return Formula.parse(old)

