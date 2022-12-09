import z3

# ------------------------------------------------------------------------
# x, y = z3.Reals("x y")
# s = z3.Solver()
# s.add(y == (x + 2))
# s.add(z3.ForAll([y], z3.Implies(y <= 0, x > y)))

# ------------------------------------------------------------------------
x = z3.Int('x')
y = z3.Real('y')
v = z3.Int('v')
s = z3.Solver()

s.add(v >= 3)
s.add(v <= 10)

xdomain = z3.And(x >= 0, x <= 10)
ydomain = z3.And(y >= 0, y <= 10, 2 * y == v)
spec = z3.Implies(x < y, x == 0)
req = z3.And(*[z3.Implies(z3.And(xdomain, ydomain), spec)])

s.add(z3.ForAll([x], z3.Exists([y], req)))

# ------------------------------------------------------------------------
# x = z3.Int('x')
# y = z3.Real('y')
# v = z3.Int('v')

# search_constraints = z3.And(v >= 0, v <= 10)
# vdomain = z3.And(z3.And(x >= 0, x <= 10), z3.And(y >= 0, y <= 10))
# environment = z3.And(2 * y == v, x < y)
# desired = x == 0
# specification = z3.Implies(z3.And(vdomain, environment), desired)

# s = z3.Solver()
# s.add(search_constraints)
# s.add(z3.ForAll([x, y], specification))

sat = s.check()
if(str(sat) == "sat"):
    print(s.model())
else:
    print("unsat")

import ipdb; ipdb.set_trace()
