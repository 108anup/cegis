import z3
from pyz3_utils.common import bcolors
from pyz3_utils.my_solver import MySolver


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
