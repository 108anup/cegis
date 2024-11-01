import math
import pandas as pd
import os
import logging
import time
from dataclasses import dataclass
from typing import Dict, List, Optional, Tuple

import z3
from pyz3_utils import MySolver
from pyz3_utils.common import GlobalConfig

from cegis import Cegis, get_unsat_core, remove_solution, sanity_checks, silent_remove_file

from .util import tcolor

logger = logging.getLogger('multi_cegis')
GlobalConfig().default_logger_setup(logger)


@dataclass
class VerifierStruct:
    verifier_name: str

    verifier_vars: List[z3.ExprRef]
    definition_vars: List[z3.ExprRef]

    definitions: z3.ExprRef
    specification: z3.ExprRef

    @staticmethod
    def run_verifier(
        verifier: MySolver
    ) -> Tuple[z3.CheckSatResult, Optional[z3.ModelRef]]:
        return Cegis.run_verifier(verifier)

    @staticmethod
    def get_counter_example_str(counter_example: z3.ModelRef,
                                verifier_vars: List[z3.ExprRef]) -> str:
        return Cegis.get_counter_example_str(counter_example, verifier_vars)

    @staticmethod
    def get_verifier_view(
            counter_example: z3.ModelRef, verifier_vars: List[z3.ExprRef],
            definition_vars: List[z3.ExprRef]) -> str:
        return Cegis.get_verifier_view(
            counter_example, verifier_vars, definition_vars)

    @staticmethod
    def get_generator_view(
            solution: z3.ModelRef, generator_vars: List[z3.ExprRef],
            definition_vars: List[z3.ExprRef], n_cex: int) -> str:
        return Cegis.get_generator_view(
            solution, generator_vars, definition_vars, n_cex)


class MultiCegis(Cegis):
    critical_generator_vars: List[z3.ExprRef]

    n_verifiers: int = 1
    verifier_structs: List[VerifierStruct]
    verifiers: List[MySolver] = []

    # Which verifier produced this cex.
    # Useful for debugging repeat cex/solution
    # and unintended removal of solution.
    vsn_for_n_cex: Dict[int, int] = dict()

    def __init__(
            self, generator_vars: List[z3.ExprRef],
            search_constraints: z3.ExprRef,
            critical_generator_vars: List[z3.ExprRef],
            verifier_structs: List[VerifierStruct],
            ctx: z3.Context, known_solution: Optional[z3.ExprRef] = None,
            solution_log_path: Optional[str] = None,
            run_log_path: Optional[str] = None,
            incremental_verify: bool = False):
        self.generator_vars = generator_vars
        self.critical_generator_vars = critical_generator_vars
        self.search_constraints = search_constraints
        self.ctx = ctx
        self.known_solution = known_solution
        self.incremental_verify = incremental_verify

        # Get rid of old API to prevent accidental use Unfortunately this only
        # helps at runtime. pyright still thinks these attributes are defined
        # :(, Is there any way to tell pyright, these are undefined.
        assert(not hasattr(self, 'verifier'))
        assert(not hasattr(self, 'verifier_vars'))
        assert(not hasattr(self, 'definition_vars'))
        assert(not hasattr(self, 'definitions'))
        assert(not hasattr(self, 'specification'))

        self.verifier_structs = verifier_structs
        self.n_verifiers = len(verifier_structs)
        for _ in self.verifier_structs:
            _verifier = MySolver(ctx)
            _verifier.warn_undeclared = False
            self.verifiers.append(_verifier)
        self.generator = MySolver(ctx)
        self.generator.warn_undeclared = False
        self.solution_log_path = solution_log_path
        self.run_log_path = run_log_path

        silent_remove_file(self.solution_log_path)
        silent_remove_file(self.run_log_path)

    # TODO: Not yet refactored. I.e., cannot debug known solution getting
    #  removed from search space.
    def check_known_solution(self):
        raise NotImplementedError

    def check_known_solution_against_each_cex(self):
        raise NotImplementedError

    def sim_known_solution_against_cex(self):
        raise NotImplementedError

    # TODO: Consider just having a get_verifier_struct function that all
    #  overridden functions below can call.

    def _bookkeep_cex(self, counter_example: z3.ModelRef,
                      candidate_solution: z3.ModelRef,
                      vsn: int):
        vs = self.verifier_structs[vsn]
        super()._bookkeep_cex(
            counter_example, candidate_solution,
            vs.verifier_vars, vs.get_counter_example_str)
        # Need to additionally save which verifeir produced this cex.
        self.vsn_for_n_cex[self._n_counter_examples] = vsn

    def log_cex_repeated_views(self, counter_example: z3.ModelRef, cex_hash: str,
                               candidate_solution: z3.ModelRef):
        old_n_cex = self.n_cex_for_cex[cex_hash]
        vsn = self.vsn_for_n_cex[old_n_cex]
        vs = self.verifier_structs[vsn]
        return self._log_cex_repeated_views(
            counter_example, cex_hash, candidate_solution,
            vs.verifier_vars, vs.definition_vars,
            vs.get_verifier_view, vs.get_generator_view)

    def log_solution_repeated_views(
            self, candidate_solution: z3.ModelRef, candidate_hash: str):
        old_n_cex = self.n_cex_for_cs[candidate_hash]
        vsn = self.vsn_for_n_cex[old_n_cex]
        vs = self.verifier_structs[vsn]
        return self._log_solution_repeated_views(
            candidate_solution, candidate_hash, vs.verifier_vars,
            vs.definition_vars, vs.get_verifier_view,
            vs.get_generator_view)

    def remove_solution(self, solution: z3.ModelRef):
        return remove_solution(self.generator, solution,
                               self.critical_generator_vars, self.ctx,
                               self._n_proved_solutions, model_completion=True)

    def log_iteration(self, itr):
        if(self.run_log_path is None):
            return
        run_entry = {
            'timestamp': time.time(),
            'iterations': itr,
            'counterexamples': self._n_counter_examples,
            'solutions': self._n_proved_solutions,
            'generator_checks': self.generator.num_checks,
            'generator_time': self.generator.total_check_time,
        }
        for i, vs in enumerate(self.verifier_structs):
            _v = self.verifiers[i]
            name = vs.verifier_name
            run_entry[f'verifier_{name}_checks'] = _v.num_checks
            run_entry[f'verifier_{name}_time'] = _v.total_check_time

        run_df = pd.DataFrame([run_entry])
        write_header = not os.path.exists(self.run_log_path)
        run_df.to_csv(self.run_log_path, mode='a',
                      header=write_header, index=False)

    def is_last_vsn(self, vsn: int):
        return vsn == self.n_verifiers - 1

    def sanity_checks(self):
        for vs in self.verifier_structs:
            sanity_checks(self.generator_vars, vs.verifier_vars,
                          vs.definition_vars, self.search_constraints,
                          vs.definitions, vs.specification)

    def run(self):
        # self.sanity_checks()
        start = time.time()
        self.generator.add(self.search_constraints)
        for vsn, vs in enumerate(self.verifier_structs):
            _verifier = self.verifiers[vsn]
            _verifier.add(z3.And(vs.definitions, z3.Not(vs.specification)))

        itr = 0
        while(True):
            itr += 1
            self.log_iteration(itr)

            logger.info("-"*80)
            logger.info("Iteration: {} ({} solution, {} counterexamples)"
                        .format(itr, len(self.solutions),
                                len(self.counter_examples)))

            # Generator
            # TODO: not refactored.
            # self.check_known_solution()
            candidate_qres = self.get_candidate_solution()

            if(not candidate_qres.is_sat()):
                logger.info(tcolor.generator("No more solutions found"))
                logger.info("Final solutions:")
                for sid, solution in enumerate(self.solutions):
                    logger.info("{}: {}".format(sid, tcolor.proved(solution)))

                end = time.time()
                logger.info("Took {:.6f} secs.".format(end - start))

                # unsat_core = get_unsat_core(self.generator)
                # import ipdb; ipdb.set_trace()
                break

            # else:
            # Check all verifiers one by one
            # Until one of the verifiers produces a counterexample
            # Or the solution passes all of them
            assert candidate_qres.model is not None
            candidate_str = self._bookkeep_cs(candidate_qres.model)

            for vsn, vs in enumerate(self.verifier_structs):
                _verifier = self.verifiers[vsn]
                counter_qres = self.get_counter_example(
                    _verifier, candidate_qres.model,
                    self.generator_vars, self.ctx, vs.run_verifier,
                    self.incremental_verify)

                if(counter_qres.is_sat()):
                    assert counter_qres.model is not None
                    self._bookkeep_cex(
                        counter_qres.model, candidate_qres.model, vsn)
                    Cegis.encode_counter_example(
                        self.generator, vs.definitions, vs.specification,
                        counter_qres.model, vs.verifier_vars,
                        vs.definition_vars, self.ctx, self._n_counter_examples)
                    break
                # else:
                #     unsat_core = get_unsat_core(_verifier)
                #     import ipdb; ipdb.set_trace()
            else:
                # All verifiers passed. Continue finding more solutions
                logger.info("Proved solution: \n{}".format(
                    tcolor.proved(candidate_str)))
                self.solutions.add(candidate_str)
                self.log_proved_solution(candidate_qres.model)
                self._n_proved_solutions += 1

                self.remove_solution(candidate_qres.model)

        itr += 1
        self.log_iteration(itr)
