import pandas as pd
import os
import logging
import time
import z3
from typing import Callable, List, Optional
from cegis import silent_remove_file
from cegis.util import profile_function, tcolor, write_solver
from pyz3_utils.common import GlobalConfig

from pyz3_utils.my_solver import MySolver


logger = logging.getLogger('smt')
GlobalConfig().default_logger_setup(logger)


GetSolutionStrType = Callable[
    [z3.ModelRef, List[z3.ExprRef], int], str]


def block_model(s: MySolver, m: z3.ModelRef, terms: List[z3.ExprRef]):
    # https://theory.stanford.edu/~nikolaj/programmingz3.html#sec-quantifiers-and-lambda-binding
    s.add(z3.Or(*[t != m.eval(t) for t in terms]))


def all_smt(s, initial_terms):

    def block_term(s, m, t):
        s.add(t != m.eval(t, model_completion=True))

    def fix_term(s, m, t):
        s.add(t == m.eval(t, model_completion=True))

    def all_smt_rec(terms):
        if z3.sat == s.check():
            m = s.model()
            yield m
            for i in range(len(terms)):
                s.push()
                block_term(s, m, terms[i])
                for j in range(i):
                    fix_term(s, m, terms[j])
                yield from all_smt_rec(terms[i:])
                s.pop()
    yield from all_smt_rec(list(initial_terms))


class ExistsForall:
    """
    Directly use SMT solver z3 for solving the there exists forall formula.
    """

    solution_strs: List[str] = []
    solution_models: List[z3.ModelRef] = []

    _n_proved_solutions: int = 0

    def __init__(
            self, existential_vars: List[z3.ExprRef],
            universal_vars: List[z3.ExprRef],
            search_constraints: z3.ExprRef, specification: z3.ExprRef,
            critical_existential_vars: Optional[List[z3.ExprRef]],
            get_solution_str: GetSolutionStrType,
            run_log_path: Optional[str] = None):
        self.existential_vars = existential_vars
        self.universal_vars = universal_vars
        self.search_constraints = search_constraints
        self.specification = specification
        if(critical_existential_vars):
            self.critical_existential_vars = critical_existential_vars
        else:
            self.critical_existential_vars = existential_vars
        self.get_solution_str = get_solution_str
        self.run_log_path = run_log_path

        silent_remove_file(self.run_log_path)

    def create_solver(self):
        logger.info("Creating quantified SMT solver")
        s = MySolver()
        s.warn_undeclared = False
        s.add(self.search_constraints)
        s.add(z3.ForAll(self.universal_vars, self.specification))
        logger.info("Solver creation complete")
        write_solver(s, "tmp/quantified_smt_solver")
        return s

    def log_iteration(self, itr):
        if(self.run_log_path is None):
            return
        run_entry = {
            'timestamp': time.time(),
            'iterations': itr,
            'solutions': self._n_proved_solutions,
            'solver_checks': self.solver.num_checks,
            'solver_time': self.solver.total_check_time,
        }
        run_df = pd.DataFrame([run_entry])
        write_header = not os.path.exists(self.run_log_path)
        run_df.to_csv(self.run_log_path, mode='a',
                      header=write_header, index=False)

    @profile_function
    def run(self):
        s = self.create_solver()
        self.solver = s

        si = 0
        itr = 0
        while True:
            itr += 1
            self.log_iteration(itr)

            start = time.time()
            sat = s.check()
            end = time.time()
            logger.info(f"Solver returned {sat} in {end - start:.6f} secs.")

            if(str(sat) == "sat"):
                model = s.model()
                solution_str = self.get_solution_str(
                    model, self.existential_vars, 0)
                logger.info("Solution {}: \n{}".format(
                    si, tcolor.proved(solution_str)))

                self.solution_strs.append(solution_str)
                self.solution_models.append(model)
                self._n_proved_solutions += 1
                block_model(s, model, self.critical_existential_vars)
                si += 1
            else:
                break
        itr += 1
        self.log_iteration(itr)
        logger.info("No more solutions found.")

    @profile_function
    def run_all(self):
        s = self.create_solver()
        self.solver = s
        start = time.time()

        itr = 1
        self.log_iteration(itr)
        for (si, model) in enumerate(all_smt(s, self.critical_existential_vars)):
            itr += 1
            self.log_iteration(itr)

            end = time.time()
            logger.info(f"Got solution in {end - start:.6f} secs.")

            solution_str = self.get_solution_str(
                model, self.existential_vars, 0)
            logger.info("Solution {}: \n{}".format(
                si, tcolor.proved(solution_str)))

            self.solution_strs.append(solution_str)
            self.solution_models.append(model)
            self._n_proved_solutions += 1

            start = time.time()

        itr += 1
        self.log_iteration(itr)
        logger.info("No more solutions found.")
