import z3
from pyz3_utils.common import bcolors
from pyz3_utils.my_solver import MySolver


def simplify_solver(solver: MySolver):
    expr_list = solver.assertion_list
    goal = z3.Goal()
    for e in expr_list:
        goal.add(e)
    t_simplify = z3.Tactic('simplify')
    t_solve_eqs = z3.Tactic('solve-eqs')
    t_propagate = z3.Tactic('propagate-values')
    t = z3.Then(t_simplify, t_solve_eqs)
    t = t_simplify
    ret = t(goal)

    with open("simplified.txt", "w") as f:
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
