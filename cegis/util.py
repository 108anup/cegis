import time
import numpy as np
import math
import logging
from pprint import pprint
import queue
from typing import Callable, Dict, List, NamedTuple, Set, TypeVar
import z3
from pyz3_utils.binary_search import BinarySearch
from pyz3_utils.common import GlobalConfig, bcolors
from pyz3_utils.my_solver import MySolver


logger = logging.getLogger('cegis')
GlobalConfig().default_logger_setup(logger)

_KT = TypeVar('_KT')
_VT = TypeVar('_VT')


class hashabledict(Dict[_KT, _VT]):
    def __hash__(self):
        return hash(tuple(sorted(self.items())))

    def copy(self):
        return hashabledict(super(hashabledict, self).copy())


class Metric(NamedTuple):
    z3ExprRef: z3.ExprRef
    lo: float
    hi: float
    eps: float
    maximize: bool

    def name(self) -> str:
        ret = self.z3ExprRef.decl().name()
        assert isinstance(ret, str)
        return ret


def fix_metrics(solver: MySolver, metric_list: List[Metric]):
    for metric in metric_list:
        if(metric.maximize):
            solver.add(metric.z3ExprRef == metric.lo)
        else:
            solver.add(metric.z3ExprRef == metric.hi)


def optimize_multi_var(s: MySolver, optimization_list: List[Metric], quick=False):
    if(len(optimization_list) == 1):
        quick = True

    str2metric = {
        x.name(): x for x in optimization_list
    }

    tried_sets: Dict[str, Set[float]] = {
        x.name(): {x.lo} if x.maximize else {x.hi} for x in optimization_list
    }
    tried_tuples: Set[hashabledict[str, float]] = set()

    to_try: queue.Queue[hashabledict[str, float]] = queue.Queue()
    first_try = hashabledict({x.name(): x.lo if x.maximize else x.hi
                             for x in optimization_list})
    to_try.put(first_try)
    tried_tuples.add(first_try)

    all_optimal_bounds = []

    while(True):
        if(to_try.empty()):
            break
        this_try = to_try.get()
        logger.info("-"*80)
        logger.info("This Try: {}".format(this_try))

        for xname, u in this_try.items():
            x = str2metric[xname]
            # Find bound for x
            logger.info("Finding bounds for {}"
                        .format(xname))
            s.push()
            for yname, v in this_try.items():
                y = str2metric[yname]
                # Fix all other vars
                if(x != y):
                    logger.info("Setting {} to {}"
                                .format(yname, v))
                    s.add(y.z3ExprRef == v)
            optimal_bounds = optimize_var(
                s, x.z3ExprRef, x.lo, x.hi, x.eps, x.maximize)
            s.pop()
            if(x.maximize):
                optimal_value = math.floor(optimal_bounds[0]/x.eps) * x.eps
            else:
                optimal_value = math.ceil(optimal_bounds[-1]/x.eps) * x.eps
            logger.info("Found bounds for {}, {}, {}"
                        .format(xname, optimal_value, optimal_bounds))

            next_try = this_try.copy()
            next_try.update({xname: optimal_value})

            # if(optimal_value not in tried_sets[xname]):
            # import ipdb; ipdb.set_trace()
            if(next_try not in tried_tuples):
                tried_tuples.add(next_try)
                tried_sets[xname].add(optimal_value)
                if(not quick):
                    to_try.put(next_try)
                all_optimal_bounds.append(next_try)

    logger.debug(tried_sets)
    return all_optimal_bounds


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

    logger.debug("Optimizing {}.".format(variable.decl().name()))

    binary_search = BinarySearch(lo, hi, eps)
    while True:
        pt = binary_search.next_pt()
        if(pt is None):
            break

        logger.debug("Optimizing {}. Trying value: {}".format(variable.decl().name(), pt))
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
        elif(isinstance(expr, z3.ArithRef)):
            return np.nan
        else:
            raise NotImplementedError
    except z3.z3types.Z3Exception as e:
        return np.nan


def get_model_value_list(model: z3.ModelRef, l: List[z3.ExprRef]):
    ret = []
    for var in l:
        val = get_raw_value(model.eval(var))
        ret.append(val)
    return ret


def write_solver(solver: MySolver, filename: str):
    with open(filename + '.smt2', 'w') as f:
        f.write(solver.to_smt2())

    with open(filename + '.txt', 'w') as f:
        f.write(solver.assertions().sexpr())


def copy_solver(solver: MySolver):
    s = MySolver(ctx=solver.ctx)
    s.warn_undeclared = False
    for assertion in solver.assertion_list:
        s.add(assertion)
    return s


def profile_function(function):
    def wrapper(*args, **kwargs):
        start = time.time()
        function(*args, **kwargs)
        end = time.time()
        logger.info(f"{function.__name__} took {end - start:.6f} secs.")
    return wrapper


def z3_min(a: z3.ArithRef, b: z3.ArithRef):
    ret = z3.If(a < b, a, b)
    assert isinstance(ret, z3.ArithRef)
    return ret


def z3_max(a: z3.ArithRef, b: z3.ArithRef):
    ret = z3.If(a > b, a, b)
    assert isinstance(ret, z3.ArithRef)
    return ret


def z3_min_list(args: List[z3.ArithRef]):
    ret = args[0]
    for arg in args[1:]:
        ret = z3_min(ret, arg)
    return ret


def z3_max_list(args: List[z3.ArithRef]):
    ret = args[0]
    for arg in args[1:]:
        ret = z3_max(ret, arg)
    return ret


def retry_z3_mem(
        solving_function: Callable, reset_function: Callable, n_attempts=3):
    """
    Sometimes solving a z3 formula gives out of memory exception. On such
    formulas, if we reset the solver state, z3 is able to solve the formula.
    This is a helper function for resetting and retrying solving for such cases.
    """

    attempt = 0
    start = time.time()
    while(True):
        attempt += 1
        try:
            ret = solving_function()
        except z3.z3types.Z3Exception as e:
            end = time.time()
            logger.error(
                f"{solving_function.__name__}"
                f" threw error after {end - start:.6f} secs"
                f" on attempt {attempt}.")
            logger.error(f"{e}")
            if(attempt <= n_attempts):
                logger.info(
                    f"Performing {reset_function.__name__} and "
                    f"restarting {solving_function.__name__}.")
                reset_function()
            else:
                raise e
        else:
            break

    end = time.time()
    logger.info(f"{solving_function.__name__} returned"
                f" in {end-start:.6f} secs.")
    return ret


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
