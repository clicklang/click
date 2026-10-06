# Expansion loses the selected return outcome inside nested call outcomes

## Violated invariant

A verifying smart tactic must expand into simple tactics that verify the same
claim. A selected `simp` in the returned arm of nested `outcomes` verifies,
but its expansion loses the return outcome for that proof branch. This is
independent of the retained-session check for implicit grouped proofs: the
fixture already has an explicit grouped caller proof and fails before and
after that check is corrected.

## Reproduction

On `148cfc13e` with the result-binding fix, run:

```
click audit mdtests/outcomes_routes_a_throw_that_leaves_the_function.md
```

The baseline session verifies, and the helper's site passes. Audit fails at
line 39, column 21, the `simp` in the inner returned arm, with:

```
execution proof failed for `caller.contract` path 1: selected post-execution tactic has no return outcome for its proof branch
```

The C calls the same modular helper twice and returns the second result. Both
Click contracts allow an exceptional outcome, and the caller proves each
successor using nested `outcomes` blocks. The C and contracts must be preserved.

## Intended regression

Retain an audit test for every smart site in this fixture, including the inner
returned and threw arms and the outer threw arm. Reduce the proof if useful
without editing its C to accommodate expansion.

## Acceptance criteria

- Audit passes every site with bounded work and unchanged C and contracts.
- Expanded proofs pass retained-session and direct targeted verification.
- The regression runs in the ordinary gate; fix shared proof-path selection
  or expansion rather than special-casing the fixture.
