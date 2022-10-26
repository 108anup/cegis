# cegis

## How do you know your encoding is incorrect.
1. Candidate solution repeats. The constraints added to the generator don't
    remove a prior solution attempt. Potentially not substituting all verifier
    decisions, i.e., there are variabels which should be verfier variables but
    are not.

2. Counter example repeats. The generator already should have checked the
    counter example. But it seems like it did not. This will happen if the
    generator does not know the counter example properly.

    If views differ then, the definitions are perhaps not setup properly.

    If no views differ then perhaps: there are
    extra variables that generator can exploit to satisfy specificaion.

3. Known solution removed from search space. You know a solution should work,
   but the cegis loop does not output it. This happens if the generator is
   forced to satisfy arbitrary definitions (extra definitions, or some variable
   is wrongly put as a definition var.)