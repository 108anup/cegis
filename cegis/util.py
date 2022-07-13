from typing import List
import z3
from pyz3_utils.common import bcolors
from pyz3_utils.my_solver import MySolver


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
