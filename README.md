# Counter Example Guided Inductive Synthesis (CEGIS)

This is a python implementation of the program synthesis algorithm CEGIS. It
was written to be used for the tool CCmatic [NSDI24] for synthesizing
congestion control algorithms. The implementation is general enough to be used
for other purposes. We took inspiration from the CEGIS implementation in
https://github.com/marcelwa/CEGIS.

# Running/using

Please refer to `tests/test_cegis_loop.py` for an example of how to use this
tool.

# Basic CEGIS operation

In general CEGIS solves a statement of the form: does there exist an $x$ such
that forall $y$ the specification $\phi(x, y)$ holds: $\exists x \forall y
\phi(x, y)$. The CEGIS generator proposes a candidate solution $x$ and the
verifier checks if there is a $y$ for which $\phi(x, y)$ does not hold. If such
a $y$ exists, the verifier provides a counterexample. The generator then uses
this counterexample to refine its candidate solution.

To propose a candidate solution, after obtaining a set of counterexamples $Y$,
the generator solves:

$$
\bigwedge_{y^* \in Y} \phi(x, y^*)
$$

For a given candidate solution $x^*$ The verifier solves:
$$
\lnot \phi(x^*, y)
$$

We call the variables in $x$ as generator variables and the variables in $y$ as
the verifier variables.

Note, the Z3 SMT solver also has support for solving quantified formulas. We
can directly ask it to solve the formula: $\forall y \phi(x, y)$. This is a
formula on the free variable $x$. Feasible assignments to $x$ are the desired
solutions. We explored this in `cegis/quantified_smt.py`. We found our CEGIS
implementation to be faster than solving quantifier formulas directly.

# Details

This implementation extends this formulation to also include definition
variables. These are variables that are a deterministic function of the
generator and verifier variables. We can think of the formula as:
$$ \exists x \forall y \forall d. \, \psi(x, y, d) \implies \phi(x, y, d) $$

Here, $\psi(x, y, d)$ provides the definitions of variables in $d$ in terms of
$x$ and $y$. If $x$ and $y$ are fixed, then only one value of $d$ should
satisfy $\psi$. In general, one could treat $d$ as $y$. Doing so results in
substituting concrete values for $d$ in the generator. Instead these variables
could be substituted as expressions. This gives generator more information
about why a counterexample breaks a candidate solution and prunes the search
space of the generator more.

To take benefit of this the definition variables and the definitions need to
marked and provided to the CEGIS API. Note, if there are mistakes in framing
the definitions, the CEGIS loop may output results that you think are incorrect
(because your specification in code is different from the specification in your
head).

## How you may know if your definitions/specification is incorrect.
1. Candidate solution repeats. This may happen when the constraints added to
    the generator don't remove a prior solution attempt. This happens
    potentially when not all verifier decisions are provided to the generator
    and are instead left as symbols, i.e., there are variables (e.g., in
    definitions) which should be annotated as verifier variables but are not.

2. Counterexample repeats. The generator already should have checked the
    counterexample in a previous CEGIS iteration. If this happens, then there
    are at least two possibilities:

    The views of how $\phi$ evaluates for a given $x$ and $y$ differ. This
    signals that the definitions are perhaps not setup properly, i.e., the
    generator and verifier are picking different assignments to $d$ for the
    same $x$ and $y$. This should not be allowed by the definitions.

    If the views do not differ then perhaps there are extra variables (not
    marked as verifier, generator, or definitions) that are referred to in the
    specification that the generator can exploit to satisfy specification.

3. Known solution removed from search space. If you know a solution should
   work, but the CEGIS loop does not output it. This happens if the generator
   is forced to satisfy arbitrary definitions (extra definitions, or some
   variable is wrongly put as a definition variable.)

The code does trigger runtime errors if these issues are hit.

If you do not want to worry about these issues, just specify all existential
variables as generator variables, all universal variables as verifier
variables, and do not use definition variables or definitions.