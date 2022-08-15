import logging
from typing import List
import z3
from pyz3_utils.binary_search import BinarySearch
from pyz3_utils.common import GlobalConfig, bcolors
from pyz3_utils.my_solver import MySolver


logger = logging.getLogger('cegis')
GlobalConfig().default_logger_setup(logger)


def optimize_var(s: MySolver, variable: z3.ExprRef, lo, hi, eps, maximize=True):
    """
    WLOG, assume we are maximizing, Find the maximum output value of input
    variable in the range [lo, hi] (with accuracy of eps), such that the formula
    checked by solver s is unsatisfiable.

    To minimize set maximize = False.

    If we want optimum value such that s is satisfiable, just reverse polarity of maximize.
    """

    # Assert that input is function application with zero
    assert len(variable.children()) == 0
    assert variable.num_args() == 0

    """
    The binary search process assumes lo, hi map to 1 1 1... 2 2 2... 3 3 3...
    So if we want maximum value for unsat, lo/1 must be registered unsat.
    Otherwise, if lo is sat then maximum value is less than lo - eps.
    """
    sat_value_1 = 'unsat'
    sat_value_3 = 'sat'

    if(not maximize):
        sat_value_1 = 'sat'
        sat_value_3 = 'unsat'

    logger.info("Optimizing {}.".format(variable.decl().name()))

    binary_search = BinarySearch(lo, hi, eps)
    while True:
        pt = binary_search.next_pt()
        if(pt is None):
            break

        logger.info("Optimizing {}. Trying value: {}".format(variable.decl().name(), pt))
        s.push()
        s.add(variable == pt)
        sat = s.check()
        s.pop()

        if(str(sat) == sat_value_1):
            binary_search.register_pt(pt, 1)
        elif str(sat) == "unknown":
            binary_search.register_pt(pt, 2)
        else:
            assert str(sat) == sat_value_3, f"Unknown value: {str(sat)}"
            binary_search.register_pt(pt, 3)

    return binary_search.get_bounds()


def get_raw_value(expr: z3.ExprRef):
    try:
        if(isinstance(expr, z3.RatNumRef)):
            return expr.as_fraction()
        elif(isinstance(expr, z3.BoolRef)):
            return bool(expr)
        else:
            raise NotImplementedError
    except z3.z3types.Z3Exception as e:
        return "Don't Care"


def write_solver(solver: MySolver, filename: str):
    with open(filename + '.smt2', 'w') as f:
        f.write(solver.to_smt2())

    with open(filename + '.txt', 'w') as f:
        f.write(solver.assertions().sexpr())


def unroll_assertions(expression: z3.ExprRef) -> List[z3.ExprRef]:
    """
    If the input expression is And of multiple expressions,
    then this returns a list of the constituent expressions.
    This is done recursively untill the constituent expressions
    use a different z3 operation at the AST root.
    """
    ret = []
    if(z3.is_and(expression)):
        for constituent in expression.children():
            ret.extend(unroll_assertions(constituent))
    else:
        ret.append(expression)
    return ret


def simplify_solver(solver: MySolver, tactic: z3.Tactic, suffix=""):
    expr_list = solver.assertion_list
    goal = z3.Goal()
    for e in expr_list:
        goal.add(e)
    ret = tactic(goal)

    with open("simplified{}.txt".format(suffix), "w") as f:
        f.write(ret.sexpr())

    return ret


class tcolor(bcolors):
    GENERATOR = bcolors.OKCYAN
    VERIFIER = bcolors.WARNING
    CANDIDATESOLUTION = bcolors.BOLD + bcolors.OKBLUE
    PROVEDSOLUTION = bcolors.BOLD + bcolors.OKGREEN

    @staticmethod
    def generator(s: str):
        return tcolor.GENERATOR + s + bcolors.ENDC

    @staticmethod
    def verifier(s: str):
        return tcolor.VERIFIER + s + bcolors.ENDC

    @staticmethod
    def candidate(s: str):
        return tcolor.CANDIDATESOLUTION + s + bcolors.ENDC

    @staticmethod
    def proved(s: str):
        return tcolor.PROVEDSOLUTION + s + bcolors.ENDC

    @staticmethod
    def error(s: str):
        return bcolors.FAIL + s + bcolors.ENDC
