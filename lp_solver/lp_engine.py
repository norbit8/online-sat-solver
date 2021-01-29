# ------- IMPORTS -------
import numpy as np

# ------- CONSTANTS -------
NO_SOLUTION = 0
SUCCESS = 1
UNBOUNDED = 2
BLAND_RULE = 0
DANTZIG_RULE = 1
EPSILON = 0.0001


def parse_result(c_B, c_N, x_B, x_N, b):
    """
    Given the arguments below, returns the maximized target function result, and the variables values
    which maximizes it.
    :param c_B: Basis vector values.
    :param c_N: Non basic variables values.
    :param x_B: Mapping vector from basis vector B to the variable index.
    :param x_N: Mapping vector from the non-basic vector to the variable index.
    :param b: b vector.
    :return: Target function value, the vars value which maximizes it.
    """
    c = np.zeros(x_B.shape[0] + x_N.shape[0])
    x = np.zeros(x_B.shape[0] + x_N.shape[0])
    c[x_B - 1] = c_B
    c[x_N - 1] = c_N
    x[x_B - 1] = b
    return x @ c


def btran(c_N, c_B, B, A_N):
    y = c_B @ np.linalg.inv(B)  # get y
    entering_var_vector = c_N - (y @ A_N)
    print(f"entering_var_vector: {entering_var_vector}")
    return entering_var_vector


def step_3():
    pass


def step_4():
    pass


def step_5():
    pass


def blands_rule(entering_var_vector, x_N):
    mask = (entering_var_vector > 0).astype(np.int64)
    mask *= x_N
    min_value, min_index = np.max(mask), np.argmax(mask)
    for index, item in enumerate(mask):
        if item != 0:
            if item < min_value:
                min_index = index
                min_value = item
    # mask = (entering_var_vector > 0).astype(np.int64)
    # mask *= x_N
    # for index, item in enumerate(mask):
    #     if item > 0:
    #         return index
    return min_index


def lp_solver(A_N: np.array, b: np.array, c_N: np.array, strategy=DANTZIG_RULE):
    # Init mats
    number_of_normal_vars = A_N.shape[1]
    number_of_slack_vars = A_N.shape[0]
    x_N = np.arange(1, number_of_normal_vars + 1)
    x_B = np.arange(number_of_normal_vars + 1, number_of_normal_vars + 1 + number_of_slack_vars)
    B = np.eye(number_of_slack_vars, number_of_slack_vars)
    c_B = np.zeros(x_B.shape)
    # print("x_n: ", x_N, "\n x_B: ", x_B, "\nB: ", B, c_N, c_B)
    # TODO: LU-factorization on B
    # B = lu_factorization(B)
    # >> Step 0: checking feasibility <<
    if np.count_nonzero(c > EPSILON) == 0:
        return NO_SOLUTION, None
    iter = 1
    while True:  # START REVISED-SIMPLEX ALGORITHM
        print(f"----------Iteration number: {iter}--------------")
        print("x_n: ", x_N,
              "\nx_B: ", x_B,
              "\nB: ", B,
              "\nc_N: ", c_N,
              "\nc_B: ", c_B,
              "\nA_N:", A_N)


        # >> Step 1: BTRAN <<
        # TODO: use eta matrices
        entering_var_vector = btran(c_N, c_B, B, A_N)
        # >> Step 2: getting the entering variable <<
        entering_var = 0
        if np.count_nonzero(entering_var_vector > EPSILON) == 0:  # FOUND OPTIMAL
            return SUCCESS, parse_result(c_B, c_N, x_B, x_N, b)
        if strategy == BLAND_RULE:
            entering_var = blands_rule(entering_var_vector, x_N)
            # print(f"{x_N},\n{entering_var_vector}\nCHOSEN ONE: {entering_var}")
        elif strategy == DANTZIG_RULE:
            entering_var = np.argmax(entering_var_vector)
        # TODO: delete me, it's a debug because Dr.Guy chose this entering var in his example
        # if iter == 1:
        #     entering_var = 2
        #     print(x_N)
        # if iter == 2:
        #     entering_var = 0
        # if iter == 3:
        #     entering_var = 3
        # >> Step 3: FTRAN <<
        # TODO: use eta matrices
        d = np.linalg.inv(B) @ A_N[:, entering_var]
        # >> Step 4: Find the largest t s.t. b - td >= 0 thus getting the leaving variable <<
        leaving_var, t = np.argmin(b / d), np.min(b / d)
        print("leaving_var: ", leaving_var)
        print("entering_var:", entering_var)
        print("d:", d)
        print("b:", b)
        print("hilok: ", b / d)
        if np.count_nonzero(d < 0) != 0:  # d cant be negative
            return UNBOUNDED, None
        # >> Step 5: Swap the entering/leaving columns in B and A_N and in x_B and x_N <<
        c_N[entering_var], c_B[leaving_var] = c_B[leaving_var], c_N[entering_var]
        B[:, leaving_var], A_N[:, entering_var] = np.copy(A_N[:, entering_var]), np.copy(B[:, leaving_var])
        x_B[leaving_var], x_N[entering_var] = x_N[entering_var], x_B[leaving_var]
        # >> Step 6: Set the value of the entering variable to t and update b <<
        b = b - d * t
        b[leaving_var] = t
        iter += 1
        print("last b:", b)

        print("SO FAR:", parse_result(c_B, c_N, x_B, x_N, b))
        print("-------------------------------------------------")


if __name__ == "__main__":
    # CLASS EXAMPLE
    A = np.array([[3, 2, 1, 2], [1, 1, 1, 1], [4, 3, 3, 4]])
    b = np.array([225, 117, 420])
    c = np.array([19, 13, 12, 17])
    # -------------
    res, val = lp_solver(A, b, c, BLAND_RULE)
    if res == UNBOUNDED:
        print("UNBOUNDED")
    elif res == SUCCESS:
        print(f"SUCCESS\nMaximal value is: {val}")
    else:
        print("NO SOLUTION")
