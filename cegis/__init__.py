import logging
import time
from dataclasses import dataclass
from typing import Any, Dict, List, Optional, Tuple

import z3
from pyz3_utils.common import GlobalConfig
from pyz3_utils.my_solver import MySolver

from .util import (get_raw_value, simplify_solver, tcolor, unroll_assertions,
                   write_solver)

logger = logging.getLogger('cegis')
GlobalConfig().default_logger_setup(logger)


NAME_TEMPLATE = "{}__cex"


def substitute_values(var_list: List[z3.ExprRef], model: z3.ModelRef,
                      name_template: str, ctx: z3.Context) -> z3.ExprRef:
    """
    Returns an expression that constrains values of variables in var_list
    to those in the model. Variables in var_list are renamed using
    name_template in the returned expression.
    """
    expr_list = []
    for v in var_list:
        name = name_template.format(v.decl().name())
        expr_list.append(z3.Const(name, v.sort()) == model.eval(v))
    expr = z3.And(*expr_list)
    assert isinstance(expr, z3.BoolRef)
    return expr


def rename_vars(
        expr: z3.ExprRef, var_list: List[z3.ExprRef],
        name_template: str):
    """
    For variables in var_list, rename their occerence in expr
    using provided name_template.
    """
    substitutions = []
    for v in var_list:
        new_name = name_template.format(v.decl().name())
        v_new = z3.Const(new_name, v.sort())
        substitutions.append((v, v_new))
    return z3.substitute(expr, *substitutions)


def remove_solution(
        solver: MySolver, solution: z3.ModelRef,
        var_list: List[z3.ExprRef], ctx: z3.Context):
    solution_value_constr = substitute_values(
        var_list, solution, "{}", ctx)
    solver.add(z3.Not(solution_value_constr))


def get_model_hash(model: z3.ModelRef, var_list: List[z3.ExprRef]):
    str_list = []
    for v in var_list:
        str_list.append("{} == {}".format(v.decl().name(), model.eval(v)))
    return ", ".join(str_list)


@dataclass
class QueryResult:
    sat: z3.CheckSatResult
    model: Optional[z3.ModelRef]
    config: Any  # For future use

    def is_sat(self):
        return str(self.sat) == "sat"


class Cegis():
    generator_vars: List[z3.ExprRef]
    verifier_vars: List[z3.ExprRef]
    definition_vars: List[z3.ExprRef]

    search_constraints: z3.ExprRef
    definitions: z3.ExprRef
    specification: z3.ExprRef
    known_solution: Optional[z3.ExprRef]

    ctx: z3.Context

    verifier: MySolver
    generator: MySolver

    _n_counter_examples: int = 0

    candidate_solutions = set()
    solutions = set()

    counter_examples = set()
    counter_example_models: List[z3.ModelRef] = list()

    cex_for_cs: Dict[str, int] = dict()

    def __init__(
            self, generator_vars: List[z3.ExprRef],
            verifier_vars: List[z3.ExprRef],
            definition_vars: List[z3.ExprRef], search_constraints: z3.ExprRef,
            definitions: z3.ExprRef, specification: z3.ExprRef,
            ctx: z3.Context, known_solution: Optional[z3.ExprRef] = None):
        self.generator_vars = generator_vars
        self.verifier_vars = verifier_vars
        self.definition_vars = definition_vars
        self.specification = specification
        self.definitions = definitions
        self.search_constraints = search_constraints
        self.ctx = ctx
        self.known_solution = known_solution

        self.verifier = MySolver(ctx)
        self.verifier.warn_undeclared = False
        self.generator = MySolver(ctx)
        self.generator.warn_undeclared = False

    def check_known_solution(self):
        if(self.known_solution is None or len(self.solutions) > 0):
            return

        dummy_generator = MySolver()
        dummy_generator.warn_undeclared = False
        assertions = self.generator.assertion_list
        dummy_generator.add(z3.And(*assertions))
        dummy_generator.add(self.known_solution)

        sat = dummy_generator.check()
        if(str(sat) != "sat"):
            logger.error("Known solution does not satisfy cex")

            # Check what happens under known solution for the last cex
            last_cex = None
            if(len(self.counter_examples) > 0):
                last_cex = self.counter_example_models[-1]

            if(last_cex is None):
                logger.error("Known solution is not in search space")
            else:
                simulator = MySolver()
                simulator.warn_undeclared = False
                simulator.add(self.search_constraints)
                simulator.add(self.known_solution)
                n_cex = 1

                # Just see what happens if we try to satisfy
                # all defintions under the counter example.
                # We don't care about the specification in the simulation

                # Inlining following effect to track all assertions.
                # dummy_spec = z3.Bool('dummy_spec', self.ctx)
                # Cegis.encode_counter_example(
                #     simulator, self.definitions, dummy_spec, last_cex,
                #     self.verifier_vars, self.definition_vars, self.ctx,
                #     n_cex)

                # Track all definitions
                name_template = NAME_TEMPLATE + str(n_cex)
                counter_example_constr = substitute_values(
                    self.verifier_vars, last_cex, name_template, self.ctx)
                simulator.add(counter_example_constr)

                simulator.set(unsat_core=True)
                for definition in unroll_assertions(self.definitions):
                    name_template = NAME_TEMPLATE + str(n_cex)
                    renamed_constr = rename_vars(
                        definition, self.verifier_vars + self.definition_vars,
                        name_template)
                    simulator.add(renamed_constr)

                write_solver(simulator, "simulator")
                sat = simulator.check()
                if(str(sat) != "sat"):
                    unsat_core = simulator.unsat_core()
                    print(len(unsat_core))
                else:
                    sim_model = simulator.model()
                    sim_str = self.get_solution_str(
                        sim_model, self.generator_vars, n_cex)
                    logger.info("Simulation: \n{}".format(
                        tcolor.candidate(sim_str)))
            assert False
        else:
            logger.info("Known solution works.")

    @staticmethod
    def get_candidate_solution(generator: MySolver):
        write_solver(generator, "generator")

        start = time.time()
        sat = generator.check()
        end = time.time()
        logger.info("Generator returned {} in {:.6f} secs.".format(
            sat, end - start))

        model = None
        if(str(sat) == "sat"):
            model = generator.model()
        return QueryResult(sat, model, None)

    @staticmethod
    def run_verifier(
        verifier
    ) -> Tuple[z3.CheckSatResult, Optional[z3.ModelRef]]:
        sat = verifier.check()
        model = None
        if(str(sat) == "sat"):
            model = verifier.model()
        return sat, model

    def get_counter_example(
            self,
            verifier: MySolver, candidate_solution: z3.ModelRef,
            generator_vars: List[z3.ExprRef], ctx: z3.Context):
        verifier.push()

        # Encode candidate solution
        candidate_solution_constr = substitute_values(
            generator_vars, candidate_solution, "{}", ctx)
        verifier.add(candidate_solution_constr)

        write_solver(verifier, "verifier")

        # simplify_solver(
        #     self.verifier, z3.Tactic('propagate-values'),
        #     "_verifier_pv")

        # simplify_solver(
        #     self.verifier,
        #     z3.Then(z3.Tactic('propagate-values'),
        #             z3.Tactic('simplify')),
        #     "_verifier_pv_s")

        # simplify_solver(
        #     self.verifier,
        #     z3.Then(z3.Then(
        #         z3.Tactic('propagate-values'), z3.Tactic('simplify')),
        #         z3.Tactic('solve-eqs')),
        #     "_verifier_pv_s_seq")

        # import ipdb; ipdb.set_trace()

        start = time.time()
        sat, model = self.run_verifier(verifier=verifier)
        end = time.time()
        logger.info("Verifer returned {} in {:.6f} secs.".format(
            sat, end - start))

        verifier.pop()
        return QueryResult(sat, model, None)

    @staticmethod
    def encode_counter_example(
            generator: MySolver, definitions: z3.ExprRef,
            specification: z3.ExprRef, counter_example: z3.ModelRef,
            verifier_vars: List[z3.ExprRef], definition_vars: List[z3.ExprRef],
            ctx: z3.Context, n_cex: int):
        name_template = NAME_TEMPLATE + str(n_cex)
        counter_example_constr = substitute_values(
            verifier_vars, counter_example, name_template, ctx)
        constr = z3.And(definitions, specification)
        assert isinstance(constr, z3.ExprRef)
        renamed_constr = rename_vars(
            constr, verifier_vars + definition_vars, name_template)
        generator.add(z3.And(counter_example_constr, renamed_constr))

    @staticmethod
    def get_solution_str(solution: z3.ModelRef,
                         generator_vars: List[z3.ExprRef],
                         n_cex: int) -> str:
        return get_model_hash(solution, generator_vars)

    @staticmethod
    def get_counter_example_str(counter_example: z3.ModelRef,
                                verifier_vars: List[z3.ExprRef]) -> str:
        return get_model_hash(counter_example, verifier_vars)

    @staticmethod
    def get_verifier_view(
            counter_example: z3.ModelRef, verifier_vars: List[z3.ExprRef],
            definition_vars: List[z3.ExprRef]) -> str:
        return get_model_hash(counter_example, verifier_vars + definition_vars)

    @staticmethod
    def get_generator_view(
            solution: z3.ModelRef, generator_vars: List[z3.ExprRef],
            definition_vars: List[z3.ExprRef], n_cex: int) -> str:
        renamed_definition_vars = []
        name_template = NAME_TEMPLATE + str(n_cex)
        for def_var in definition_vars:
            renamed_var = z3.Const(
                name_template.format(def_var.decl().name), def_var.sort())
            renamed_definition_vars.append(renamed_var)
        return get_model_hash(
            solution, generator_vars + renamed_definition_vars)

    def log_solution_repeated_views(
            self, candidate_solution: z3.ModelRef, candidate_str: str):
        logger.info("="*80)
        logger.info("Debugging solution repeat")
        old_n_cex = self.cex_for_cs[candidate_str]
        old_counter_example = self.counter_example_models[old_n_cex-1]

        vview = self.get_verifier_view(
            old_counter_example, self.verifier_vars,
            self.definition_vars)
        logger.info("Verifer view of repeat solution:\n{}"
                    .format(tcolor.verifier(vview)))

        gview = self.get_generator_view(
            candidate_solution, self.generator_vars,
            self.definition_vars, old_n_cex)
        logger.info("Generator view of repeat solution:\n{}"
                    .format(tcolor.generator(gview)))

        name_template = NAME_TEMPLATE + str(old_n_cex)
        differing_vars = []
        for dvar in self.definition_vars:
            gvar = z3.Const(
                name_template.format(dvar.decl().name()), dvar.sort())
            gval = get_raw_value(candidate_solution.eval(gvar))
            vval = get_raw_value(old_counter_example.eval(dvar))
            if(gval != vval):
                differing_vars.append(dvar.decl().name())
        logger.info(tcolor.error(
            "Views differ for: {}".format(differing_vars)))

    def _bookkeep_cs(self, candidate_solution: z3.ModelRef):
        candidate_str = self.get_solution_str(
            candidate_solution, self.generator_vars, self._n_counter_examples)
        logger.info("Candidate solution: \n{}".format(
            tcolor.candidate(candidate_str)))
        if(candidate_str in self.candidate_solutions):
            logger.error("Candidate solution repeated")
            self.log_solution_repeated_views(candidate_solution, candidate_str)
            assert False
        else:
            self.candidate_solutions.add(candidate_str)
            # This is the counter example number that will be used
            # for the counter example that breaks this candidate_str
            self.cex_for_cs[candidate_str] = self._n_counter_examples + 1
            return candidate_str

    def _bookkeep_cex(self, counter_example: z3.ModelRef):
        self._n_counter_examples += 1
        cex_str = self.get_counter_example_str(
            counter_example, self.verifier_vars)
        logger.info("Counter example: \n{}".format(
            tcolor.verifier(cex_str)))
        assert cex_str not in self.counter_examples, (
            "Counter examples repeated")
        self.counter_examples.add(cex_str)
        self.counter_example_models.append(counter_example)

    def run(self):
        start = time.time()
        self.generator.add(self.search_constraints)
        self.verifier.add(z3.And(self.definitions, z3.Not(self.specification)))

        itr = 1
        while(True):
            logger.info("-"*80)
            logger.info("Iteration: {}".format(itr))

            # Generator
            self.check_known_solution()
            candidate_qres = Cegis.get_candidate_solution(self.generator)

            if(not candidate_qres.is_sat()):
                logger.info(tcolor.generator("No more solutions found"))
                logger.info("Final solutions:")
                for sid, solution in enumerate(self.solutions):
                    logger.info("{}: {}".format(sid, tcolor.proved(solution)))

                end = time.time()
                logger.info("Took {:.6f} secs.".format(end - start))
                # simplify_solver(
                #     self.generator, z3.Tactic('propagate-values'),
                #     "_generator")
                # import ipdb; ipdb.set_trace()
                break

            # else:
            # Verifier
            assert candidate_qres.model is not None
            candidate_str = self._bookkeep_cs(candidate_qres.model)
            counter_qres = self.get_counter_example(
                self.verifier, candidate_qres.model,
                self.generator_vars, self.ctx)

            if(not counter_qres.is_sat()):
                logger.info("Proved solution: \n{}".format(
                    tcolor.proved(candidate_str)))
                self.solutions.add(candidate_str)

                remove_solution(self.generator, candidate_qres.model,
                                self.generator_vars, self.ctx)

            else:
                assert counter_qres.model is not None
                self._bookkeep_cex(counter_qres.model)
                Cegis.encode_counter_example(
                    self.generator, self.definitions, self.specification,
                    counter_qres.model, self.verifier_vars,
                    self.definition_vars, self.ctx, self._n_counter_examples)

            itr += 1
