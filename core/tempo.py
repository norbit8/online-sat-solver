from Formula import *


def helper_nnf(formula: Formula):
    if is_variable(str(formula)) or is_constant(str(formula)):
        return formula
    if formula.root == "~":
        removed_neg_formula = formula.first
        if removed_neg_formula.root == '|':
            if removed_neg_formula.first.root == "~" and removed_neg_formula.second.root == "~":
                return Formula.parse(
                    "(" + str(removed_neg_formula.first.first) + "&" + str(removed_neg_formula.second.first) + ")")
            if removed_neg_formula.first.root == "~":
                return Formula.parse(
                    "(" + str(removed_neg_formula.first.first) + "&" + str(helper_nnf(
                        Formula.parse("~" + str(removed_neg_formula.second)))) + ")")
            if removed_neg_formula.second.root == "~":
                return Formula.parse(
                    "(" + str(helper_nnf(Formula.parse("~" + str(removed_neg_formula.first)))) + "&" + str(
                        removed_neg_formula.second.first) + ")")
            return Formula.parse(
                "(" + str(helper_nnf(Formula.parse("~" + str(removed_neg_formula.first)))) + "&" + str(
                    helper_nnf(Formula.parse("~" + str(removed_neg_formula.second)))) + ")")
        elif removed_neg_formula.root == '&':
            if removed_neg_formula.first.root == "~" and removed_neg_formula.second.root == "~":
                return Formula.parse(
                    "(" + str(removed_neg_formula.first.first) + "|" + str(removed_neg_formula.second.first) + ")")
            elif removed_neg_formula.first.root == "~":
                return Formula.parse(
                    "(" + str(removed_neg_formula.first.first) + "|" + str(
                        helper_nnf(Formula.parse("~" + str(removed_neg_formula.second)))) + ")")
            elif removed_neg_formula.second.root == "~":
                return Formula.parse(
                    "(" + str(helper_nnf(Formula.parse("~" + str(removed_neg_formula.first)))) + "|" + str(
                        removed_neg_formula.second.first) + ")")
            return Formula.parse(
                "(" + str(helper_nnf(Formula.parse("~" + str(removed_neg_formula.first)))) + "|" + str(
                    helper_nnf(Formula.parse("~" + str(removed_neg_formula.second)))) + ")")
    if formula.root == "->":
        if formula.first.root == "~":
            return Formula.parse("(" + str(formula.first.first) + "|" + str(formula.second) + ")")
        return Formula.parse(
            "(" + str(helper_nnf(Formula.parse("~" + str(formula.first)))) + "|" + str(formula.second) + ")")
    if formula.root == "<->":
        return Formula.parse(
            "(" + str(helper_nnf(Formula.parse("(" + str(formula.first) + "->" + str(formula.second) + ")"))) + "&" +
            str(helper_nnf(Formula.parse("(" + str(formula.second) + "->" + str(formula.first) + ")"))) + ")")
    # if formula.root == "&" or formula.root == '|'
    return formula


def convert_to_nnf(formula: Formula):
    print("STEP: ", formula)
    if is_constant(str(formula)) or is_variable(str(formula)):
        return formula
    # unary operator
    if formula.root == "~":
        if is_constant(str(formula.first)) or is_variable(str(formula.first)):
            return formula
        elif formula.first.root == '~':
            return convert_to_nnf(formula.first.first)
        else:  # Binary op is the root after ~, so we are in the case of ~(q->p) for example.
            removed_negation_formula = formula.first
            op = removed_negation_formula.root
            return helper_nnf(Formula.parse("~" + str(helper_nnf(
                Formula.parse(
                    "(" + str(convert_to_nnf(removed_negation_formula.first)) + op + str(
                        convert_to_nnf(removed_negation_formula.second)) + ")")))))
    # binary operator
    op = formula.root
    return helper_nnf(
        Formula.parse("(" + str(convert_to_nnf(formula.first)) + op + str(convert_to_nnf(formula.second)) + ")"))


def convert_to_cnf(formula: List[Formula]):
    new_cnf = [formula[0]]
    for f in formula[1:]:
        if f.second.root == "~":
            dictionary = dict({'q': f.second.first, 'p': f.first})
            new_cnf.append(Formula.substitute_variables(Formula.parse("(q|p)"), dictionary))
            new_cnf.append(Formula.substitute_variables(Formula.parse("(~p|~q)"), dictionary))
        elif f.second.root == "->":
            dictionary = dict({'r': f.second.second, 'q': f.second.first, 'p': f.first})
            if dictionary['q'].root == "~" and dictionary['r'].root == "~":
                dictionary['r'] = dictionary['r'].first
                dictionary['q'] = dictionary['q'].first
                new_cnf.append(Formula.substitute_variables(Formula.parse("(~r|(~p|q))"), dictionary))
                new_cnf.append(Formula.substitute_variables(Formula.parse("(~q|p)"), dictionary))
                new_cnf.append(Formula.substitute_variables(Formula.parse("(r|p)"), dictionary))
            elif dictionary['q'].root == "~":
                dictionary['q'] = dictionary['q'].first
                new_cnf.append(Formula.substitute_variables(Formula.parse("(r|(~p|q))"), dictionary))
                new_cnf.append(Formula.substitute_variables(Formula.parse("(~q|p)"), dictionary))
                new_cnf.append(Formula.substitute_variables(Formula.parse("(~r|p)"), dictionary))
            elif dictionary['r'].root == "~":
                dictionary['r'] = dictionary['r'].first
                new_cnf.append(Formula.substitute_variables(Formula.parse("(~r|(~p|~q))"), dictionary))
                new_cnf.append(Formula.substitute_variables(Formula.parse("(q|p)"), dictionary))
                new_cnf.append(Formula.substitute_variables(Formula.parse("(r|p)"), dictionary))
            else:
                new_cnf.append(Formula.substitute_variables(Formula.parse("(r|(~p|~q))"), dictionary))
                new_cnf.append(Formula.substitute_variables(Formula.parse("(q|p)"), dictionary))
                new_cnf.append(Formula.substitute_variables(Formula.parse("(~r|p)"), dictionary))
        elif f.second.root == "&":
            dictionary = dict({'r': f.second.second, 'q': f.second.first, 'p': f.first})
            if dictionary['q'].root == "~" and dictionary['r'].root == "~":
                dictionary['r'] = dictionary['r'].first
                dictionary['q'] = dictionary['q'].first
                new_cnf.append(Formula.substitute_variables(Formula.parse("(q|(r|p))"), dictionary))
                new_cnf.append(Formula.substitute_variables(Formula.parse("(~q|~p)"), dictionary))
                new_cnf.append(Formula.substitute_variables(Formula.parse("(~p|~r)"), dictionary))
            elif dictionary['q'].root == "~":
                dictionary['q'] = dictionary['q'].first
                new_cnf.append(Formula.substitute_variables(Formula.parse("(q|(~r|p))"), dictionary))
                new_cnf.append(Formula.substitute_variables(Formula.parse("(~q|~p)"), dictionary))
                new_cnf.append(Formula.substitute_variables(Formula.parse("(~p|r)"), dictionary))
            elif dictionary['r'].root == "~":
                dictionary['r'] = dictionary['r'].first
                new_cnf.append(Formula.substitute_variables(Formula.parse("(~q|(r|p))"), dictionary))
                new_cnf.append(Formula.substitute_variables(Formula.parse("(q|~p)"), dictionary))
                new_cnf.append(Formula.substitute_variables(Formula.parse("(~p|~r)"), dictionary))
            else:
                new_cnf.append(Formula.substitute_variables(Formula.parse("(~q|(~r|p))"), dictionary))
                new_cnf.append(Formula.substitute_variables(Formula.parse("(q|~p)"), dictionary))
                new_cnf.append(Formula.substitute_variables(Formula.parse("(~p|r)"), dictionary))
        elif f.second.root == "|":
            dictionary = dict({'r': f.second.second, 'q': f.second.first, 'p': f.first})
            if dictionary['q'].root == "~" and dictionary['r'].root == "~":
                dictionary['r'] = dictionary['r'].first
                dictionary['q'] = dictionary['q'].first
                new_cnf.append(Formula.substitute_variables(Formula.parse("(~r|(~p|~q))"), dictionary))
                new_cnf.append(Formula.substitute_variables(Formula.parse("(q|p)"), dictionary))
                new_cnf.append(Formula.substitute_variables(Formula.parse("(r|p)"), dictionary))
            elif dictionary['q'].root == "~":
                dictionary['q'] = dictionary['q'].first
                new_cnf.append(Formula.substitute_variables(Formula.parse("(r|(~p|~q))"), dictionary))
                new_cnf.append(Formula.substitute_variables(Formula.parse("(q|p)"), dictionary))
                new_cnf.append(Formula.substitute_variables(Formula.parse("(~r|p)"), dictionary))
            elif dictionary['r'].root == "~":
                dictionary['r'] = dictionary['r'].first
                new_cnf.append(Formula.substitute_variables(Formula.parse("(~r|(~p|q))"), dictionary))
                new_cnf.append(Formula.substitute_variables(Formula.parse("(~q|p)"), dictionary))
                new_cnf.append(Formula.substitute_variables(Formula.parse("(r|p)"), dictionary))
            else:
                new_cnf.append(Formula.substitute_variables(Formula.parse("(r|(~p|q))"), dictionary))
                new_cnf.append(Formula.substitute_variables(Formula.parse("(~q|p)"), dictionary))
                new_cnf.append(Formula.substitute_variables(Formula.parse("(~r|p)"), dictionary))
        elif f.second.root == "<->":
            dictionary = dict({'r': f.second.second, 'q': f.second.first, 'p': f.first})
            if dictionary['q'].root == "~" and dictionary['r'].root == "~":
                dictionary['r'] = dictionary['r'].first
                dictionary['q'] = dictionary['q'].first
                new_cnf.append(Formula.substitute_variables(Formula.parse("(q|(r|p))"), dictionary))
                new_cnf.append(Formula.substitute_variables(Formula.parse("(~q|(~r|p))"), dictionary))
                new_cnf.append(Formula.substitute_variables(Formula.parse("(r|(~q|~p))"), dictionary))
                new_cnf.append(Formula.substitute_variables(Formula.parse("(q|(~r|~p))"), dictionary))
            elif dictionary['q'].root == "~":
                dictionary['q'] = dictionary['q'].first
                new_cnf.append(Formula.substitute_variables(Formula.parse("(q|(~r|p))"), dictionary))
                new_cnf.append(Formula.substitute_variables(Formula.parse("(~q|(r|p))"), dictionary))
                new_cnf.append(Formula.substitute_variables(Formula.parse("(~r|(~q|~p))"), dictionary))
                new_cnf.append(Formula.substitute_variables(Formula.parse("(q|(r|~p))"), dictionary))
            elif dictionary['r'].root == "~":
                dictionary['r'] = dictionary['r'].first
                new_cnf.append(Formula.substitute_variables(Formula.parse("(~q|(r|p))"), dictionary))
                new_cnf.append(Formula.substitute_variables(Formula.parse("(q|(~r|p))"), dictionary))
                new_cnf.append(Formula.substitute_variables(Formula.parse("(r|(q|~p))"), dictionary))
                new_cnf.append(Formula.substitute_variables(Formula.parse("(~q|(~r|~p))"), dictionary))
            else:
                new_cnf.append(Formula.substitute_variables(Formula.parse("(~q|(~r|p))"), dictionary))
                new_cnf.append(Formula.substitute_variables(Formula.parse("(q|(r|p))"), dictionary))
                new_cnf.append(Formula.substitute_variables(Formula.parse("(~r|(q|~p))"), dictionary))
                new_cnf.append(Formula.substitute_variables(Formula.parse("(~q|(r|~p))"), dictionary))
        else:
            if f.second == '~':
                print("here",f.second.first)
                dictionary = dict({'p': f.second.first, 'q': f.first})
                new_cnf.append(Formula.substitute_variables(Formula.parse("(p|q)"), dictionary))
                new_cnf.append(Formula.substitute_variables(Formula.parse("(~q|~p)"), dictionary))
            else:
                dictionary = dict({'p': f.second, 'q': f.first})
                new_cnf.append(Formula.substitute_variables(Formula.parse("(~p|q)"), dictionary))
                new_cnf.append(Formula.substitute_variables(Formula.parse("(p|~q)"), dictionary))
    return new_cnf


if __name__ == "__main__":
    # print(Formula.parse("(p->~q)").second.first)
    # print(convert_to_cnf(Formula.parse("~(p->(p&q))")))
    print(convert_to_cnf([Formula.parse("x"), Formula.parse("(p<->(~q|~r))")]))
