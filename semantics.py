# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: propositions/semantics.py

"""Semantic analysis of propositional-logic constructs."""

from typing import AbstractSet, Iterable, Iterator, List, Mapping

from Formula import *

Model = Mapping[str, bool]

def is_model(model: Model) -> bool:
    """Checks if the given dictionary a model over some set of variables.

    Parameters:
        model: dictionary to check.

    Returns:
        ``True`` if the given dictionary is a model over some set of variables,
        ``False`` otherwise.
    """
    for key in model:
        if not (is_variable(key) and type(model[key]) is bool):
            return False
    return True

def variables(model: Model) -> AbstractSet[str]:
    """Finds all variables over which the given model is defined.

    Parameters:
        model: model to check.

    Returns:
        A set of all variables over which the given model is defined.
    """
    assert is_model(model)
    return model.keys()

def and_op(righty, lefty, model):
    righty = Formula.parse_prefix(righty[1:])[0]
    righty = evaluate(righty, model)
    return righty and lefty

def or_op(righty, lefty, model):
    righty = Formula.parse_prefix(righty[1:])[0]
    righty = evaluate(righty, model)
    return righty or lefty

def xor_op(righty, lefty, model):
    righty = Formula.parse_prefix(righty[1:])[0]
    righty = evaluate(righty, model)
    return righty != lefty

def iff_op(righty, lefty, model):
    righty = Formula.parse_prefix(righty[3:])[0]
    righty = evaluate(righty, model)
    if (lefty is False and righty is False) or (lefty is True and righty is True):
        return True
    return False

def if_op(righty, lefty, model):
    righty = Formula.parse_prefix(righty[2:])[0]
    righty = evaluate(righty, model)
    if lefty is True and righty is False:
        return False
    return True

def evaluate(formula: Formula, model: Model) -> bool:
    """Calculates the truth value of the given formula in the given model.

    Parameters:
        formula: formula to calculate the truth value of.
        model: model over (possibly a superset of) the variables of the formula,
            to calculate the truth value in.

    Returns:
        The truth value of the given formula in the given model.
    """
    assert is_model(model)
    assert formula.variables().issubset(variables(model))
    # Task 2.1
    formula_string = str(formula)
    # dot1 constant T equivalent to True
    if formula_string == "T":
        return True
    # dot1 constant F equivalent to False
    if formula_string == "F":
        return False
    # dot2 if phi is the variable p then return M(p)
    if is_variable(formula_string):
        return model[formula_string]
    # dot3 '~'
    if formula_string[0] == "~":
        false_counter = 0
        for ch in formula_string:
            if ch == "~":
                false_counter += 1
            else:
                evalue = evaluate(Formula.parse(formula_string[false_counter:]), model)
                return evalue if false_counter % 2 == 0 else not evalue
    # dot4 form of a formula >_<
    if formula_string[0] == "(":
        parsed = Formula.parse_prefix(formula_string[1:])
        lefty = evaluate(parsed[0], model)
        righty = parsed[1]
        if righty[0] == '&':
            return and_op(righty, lefty, model)
        if righty[0] == '|':
            return or_op(righty, lefty, model)
        if righty[0] == '-' and righty[1] == '>':
            return if_op(righty, lefty, model)
        if righty[0] == '-' and righty[1] == '|':
            return not(or_op(righty[1:], lefty, model))
        if righty[0] == '-' and righty[1] == '&':
            return not(and_op(righty[1:], lefty, model))
        if righty[0] == '<':
            return iff_op(righty, lefty, model)
        if righty[0] == '+':
            return xor_op(righty, lefty, model)

def all_models(variables: List[str]) -> Iterable[Model]:
    """Calculates all possible models over the given variables.

    Parameters:
        variables: list of variables over which to calculate the models.

    Returns:
        An iterable over all possible models over the given variables. The order
        of the models is lexicographic according to the order of the given
        variables, where False precedes True.

    Examples:
        >>> list(all_models(['p', 'q']))
        [{'p': False, 'q': False}, {'p': False, 'q': True}, {'p': True, 'q': False}, {'p': True, 'q': True}]
    """
    for v in variables:
        assert is_variable(v)
    # Task 2.2
    size = len(variables)
    for number in range(pow(2, size)):
        binary_rep = f'{number:>b}'.zfill(size)
        row = {}
        for index, var in enumerate(variables):
            row[var] = bool(int(binary_rep[index]))
        yield(row)

def truth_values(formula: Formula, models: Iterable[Model]) -> Iterable[bool]:
    """Calculates the truth value of the given formula in each of the given
    model.

    Parameters:
        formula: formula to calculate the truth value of.
        model: iterable over models to calculate the truth value in.

    Returns:
        An iterable over the respective truth values of the given formula in
        each of the given models, in the order of the given models.
    """
    # Task 2.3
    lst = []
    for model in models:
        lst.append(evaluate(formula, model))
    return lst

def print_truth_table(formula: Formula) -> None:
    """Prints the truth table of the given formula, with variable-name columns
    sorted alphabetically.

    Parameters:
        formula: formula to print the truth table of.

    Examples:
        >>> print_truth_table(Formula.parse('~(p&q76)'))
        | p | q76 | ~(p&q76) |
        |---|-----|----------|
        | F | F   | T        |
        | F | T   | T        |
        | T | F   | T        |
        | T | T   | F        |
    """
    # Task 2.4
    names = list(formula.variables())
    names.sort()
    models = list(all_models(names))
    print_this = []
    for index, model in enumerate(models):
        evalue = evaluate(formula, model)
        print_this.append(evalue)
    for var in names:
        print("| " + var + " ", end="")
    print("| " + str(formula) + " |")
    # top div
    for var in names:
        print("|" + len(var)*"-"+"--", end="")
    print("|" + len(str(formula))*"-"+"--" + "|")
    for index, model in enumerate(models):
        for name in names:
            print("| " + ("T" if model[name] is True else "F")  + len(name)*" " , end="")
        print("| " + ("T" if print_this[index] is True else "F") + len(str(formula))*" " + "|")

def is_tautology(formula: Formula) -> bool:
    """Checks if the given formula is a tautology.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula is a tautology, ``False`` otherwise.
    """
    # Task 2.5a
    names = list(formula.variables())
    models = list(all_models(names))
    for index, model in enumerate(models):
        if evaluate(formula, model) is False:
            return False
    return True

def is_contradiction(formula: Formula) -> bool:
    """Checks if the given formula is a contradiction.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula is a contradiction, ``False`` otherwise.
    """
    # Task 2.5b
    not_formula = Formula.parse('~' + str(formula))
    return is_tautology(not_formula)

def is_satisfiable(formula: Formula) -> bool:
    """Checks if the given formula is satisfiable.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula is satisfiable, ``False`` otherwise.
    """
    # Task 2.5c
    names = list(formula.variables())
    models = list(all_models(names))
    for index, model in enumerate(models):
        if evaluate(formula, model) is True:
            return True
    return False

def synthesize_for_model(model: Model) -> Formula:
    """Synthesizes a propositional formula in the form of a single clause that
      evaluates to ``True`` in the given model, and to ``False`` in any other
      model over the same variables.

    Parameters:
        model: model in which the synthesized formula is to hold.

    Returns:
        The synthesized formula.
    """
    assert is_model(model)
    # Task 2.6
    if len(model) == 0:
        return Formula.parse("")
    if len(model) == 1:
        for key in model:
            if model[key]:
                return Formula.parse(key)
            else:
                return Formula.parse("~" + key)
    keys = list(model.keys())
    mod = dict()
    mod[keys[0]] = model[keys[0]]
    form = synthesize_for_model(mod)
    for index in range(1, len(keys)):
        mod.clear()
        mod[keys[index]] = model[keys[index]]
        new_form = "(" + str(form) + "&" + str(synthesize_for_model(mod)) + ")"
        form = Formula.parse(new_form)
    return form

def synthesize(variables: List[str], values: Iterable[bool]) -> Formula:
    """Synthesizes a propositional formula in DNF over the given variables, from
    the given specification of which value the formula should have on each
    possible model over these variables.

    Parameters:
        variables: the set of variables for the synthesize formula.
        values: iterable over truth values for the synthesized formula in every
            possible model over the given variables, in the order returned by
            `all_models`\ ``(``\ `~synthesize.variables`\ ``)``.

    Returns:
        The synthesized formula.

    Examples:
        >>> formula = synthesize(['p', 'q'], [True, True, True, False])
        >>> for model in all_models(['p', 'q']):
        ...     evaluate(formula, model)
        True
        True
        True
        False
    """
    assert len(variables) > 0
    # Task 2.7
    if not (True in values):
        return Formula.parse("(" + variables[0] + "&~" + variables[0] + ")")
    else:
        models = list(all_models(variables))
        first_true = False
        for index, val in enumerate(values):
            if val is True and not first_true:
                res = str(synthesize_for_model(models[index]))
                first_true = True
            if val is True and first_true:
                res = "(" + res + "|" + str(synthesize_for_model(models[index])) + ")"
        return Formula.parse(res)
