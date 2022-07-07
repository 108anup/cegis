from cegis import Cegis
import z3

# \begin{align}
#     \exists v \ldotp \forall x,y \ldotp \sigma(v, x, y) \text{, where,} \nonumber\\
#     \sigma(v, x, y) = ((y = v/2 \land x < y) \implies x = 0)
# \end{align}


def test_without_ve():
    x = z3.Real('x')
    y = z3.Real('y')
    v = z3.Int('v')

    verifier_vars = [x, y]
    generator_vars = [v]
    definition_vars = []

    search_constraints = z3.And(v >= 0, v <= 10)
    definitions = True
    specification = z3.Implies(z3.And(y == v/2, x < y), x == 0)

    ctx = z3.main_ctx()
    cg = Cegis(generator_vars, verifier_vars, definition_vars,
               search_constraints, definitions, specification, ctx)
    cg.run()


def test_with_ve():
    x = z3.Real('x')
    y = z3.Real('y')
    v = z3.Real('v')

    verifier_vars = [x]
    generator_vars = [v]
    definition_vars = [y]

    search_constraints = True
    definitions = y == v/2
    specification = z3.Implies(x < y, x == 0)

    ctx = z3.main_ctx()
    cg = Cegis(generator_vars, verifier_vars, definition_vars,
               search_constraints, definitions, specification, ctx)
    cg.run()
