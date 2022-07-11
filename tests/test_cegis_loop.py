from cegis import Cegis
import z3

# \begin{align}
#     \exists v \ldotp \forall x,y \ldotp \sigma(v, x, y) \text{, where,} \nonumber\\
#     \sigma(v, x, y) = ((y = v/2 \land x < y) \implies x = 0)
# \end{align}


def test_without_ve():
    x = z3.Int('x')
    y = z3.Real('y')
    v = z3.Int('v')

    verifier_vars = [x, y]
    generator_vars = [v]
    definition_vars = []

    search_constraints = z3.And(v >= 0, v <= 10)
    vdomain = z3.And(z3.And(x >= 0, x <= 10), z3.And(y >= 0, y <= 10))
    definitions = True
    environment = z3.And(2 * y == v, x < y)
    desired = x == 0
    specification = z3.Implies(z3.And(vdomain, environment), desired)

    ctx = z3.main_ctx()
    cg = Cegis(generator_vars, verifier_vars, definition_vars,
               search_constraints, definitions, specification, ctx)
    cg.run()


def test_with_ve():
    x = z3.Int('x')
    y = z3.Real('y')
    v = z3.Int('v')

    verifier_vars = [x]
    generator_vars = [v]
    definition_vars = [y]

    search_constraints = z3.And(v >= 0, v <= 10)
    vdomain = z3.And(z3.And(x >= 0, x <= 10), z3.And(y >= 0, y <= 10))
    definitions = z3.And(2 * y == v, vdomain)
    specification = z3.Implies(x < y, x == 0)

    ctx = z3.main_ctx()
    cg = Cegis(generator_vars, verifier_vars, definition_vars,
               search_constraints, definitions, specification, ctx)
    cg.run()
