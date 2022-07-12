import logging
import time
from dataclasses import dataclass
from typing import Any, List, Optional, Tuple

import z3
from pyz3_utils.common import GlobalConfig
from pyz3_utils.my_solver import MySolver

from .util import simplify_solver, tcolor


logger = logging.getLogger('cegis')
GlobalConfig().default_logger_setup(logger)


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

    ctx: z3.Context

    verifier: MySolver
    generator: MySolver

    _n_counter_examples: int = 0

    candidate_solutions = set()
    solutions = set()

    counter_examples = set()

    def __init__(self, generator_vars, verifier_vars, definition_vars,
                 search_constraints, definitions, specification, ctx):
        self.generator_vars = generator_vars
        self.verifier_vars = verifier_vars
        self.definition_vars = definition_vars
        self.specification = specification
        self.definitions = definitions
        self.search_constraints = search_constraints
        self.ctx = ctx

        self.verifier = MySolver(ctx)
        self.verifier.warn_undeclared = False
        self.generator = MySolver(ctx)
        self.generator.warn_undeclared = False

    @staticmethod
    def get_candidate_solution(generator: MySolver):
        with open('generator.smt2', 'w') as f:
            f.write(generator.to_smt2())

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

        with open('verifier.smt2', 'w') as f:
            f.write(verifier.to_smt2())

        with open('verifier.txt', 'w') as f:
            f.write(verifier.assertions().sexpr())

        # import ipdb; ipdb.set_trace()

        start = time.time()
        sat, model = self.run_verifier(verifier)
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
        name_template = "{}__cex" + str(n_cex)
        counter_example_constr = substitute_values(
            verifier_vars, counter_example, name_template, ctx)
        constr = z3.And(definitions, specification)
        assert isinstance(constr, z3.ExprRef)
        renamed_constr = rename_vars(
            constr, verifier_vars + definition_vars, name_template)
        generator.add(z3.And(counter_example_constr, renamed_constr))

    @staticmethod
    def get_solution_str(solution: z3.ModelRef,
                         generator_vars: List[z3.ExprRef]) -> str:
        return get_model_hash(solution, generator_vars)

    @staticmethod
    def get_counter_example_str(counter_example: z3.ModelRef,
                                verifier_vars: List[z3.ExprRef]) -> str:
        return get_model_hash(counter_example, verifier_vars)

    def _bookkeep_cs(self, candidate_solution: z3.ModelRef):
        candidate_str = self.get_solution_str(
            candidate_solution, self.generator_vars)
        logger.info("Candidate solution: \n{}".format(
            tcolor.candidate(candidate_str)))
        assert candidate_str not in self.candidate_solutions, (
            "Candidate solution repeated")
        self.candidate_solutions.add(candidate_str)
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

    def run(self):
        start = time.time()
        self.generator.add(self.search_constraints)
        self.verifier.add(z3.And(self.definitions, z3.Not(self.specification)))

        itr = 1
        while(True):
            logger.info("Iteration: {}".format(itr))

            # Generator
            candidate_qres = Cegis.get_candidate_solution(self.generator)

            if(not candidate_qres.is_sat()):
                logger.info(tcolor.generator("No more solutions found"))
                logger.info("Final solutions:")
                for sid, solution in enumerate(self.solutions):
                    logger.info("{}: {}".format(sid, tcolor.proved(solution)))

                end = time.time()
                logger.info("Took {:.6f} secs.".format(end - start))
                # simplify_solver(self.generator)
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
