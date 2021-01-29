import numpy as np
from sat_solver.sat_engine import solve_sat
from prop_logic.formula import Formula
from prop_logic.semantics import evaluate, is_satisfiable

class bcolors:
    HEADER = '\033[95m'
    OKBLUE = '\033[94m'
    OKCYAN = '\033[96m'
    OKGREEN = '\033[92m'
    WARNING = '\033[93m'
    FAIL = '\033[91m'
    ENDC = '\033[0m'
    BOLD = '\033[1m'
    UNDERLINE = '\033[4m'


if __name__ == '__main__':
    # ---- TESTS ----
    operators = ['->', '<->', '&', '|']
    neg_or_not_to_neg = ['~', '']
    number_of_iterations = 1000
    N = 13
    while number_of_iterations != 0:
        f = ''
        number_of_variables = np.random.randint(N) + 2
        for i in range(number_of_variables):
            variable = neg_or_not_to_neg[np.random.randint(2)] + f'p{i}'
            op = operators[np.random.randint(len(operators))]
            if i + 1 == number_of_variables:
                f += variable + ")"
            else:
                f += '(' + variable + op
        f += ')' * (number_of_variables - 2)
        # unsat stat
        # f = "(" + f + "<->~" + f + ")"

        print("Testing the formula: ", f)
        result, final_assignment = solve_sat(f)
        print("Testing same result (SAT / UNSAT): ",
              bcolors.OKCYAN + "PASSED" + bcolors.ENDC if is_satisfiable(
                  Formula.parse(f)) == result else bcolors.WARNING + "FAILED" + bcolors.ENDC)
        if result:
            print("Testing the assigment: ", bcolors.OKCYAN + "PASSED" + bcolors.ENDC
            if evaluate(Formula.parse(f), final_assignment) is True else bcolors.WARNING + "FAILED" + bcolors.ENDC)
        number_of_iterations -= 1
        print("___________________________________________")
    # ---- TESTS END ----