# Let `intro() as name` name a range quantifier's variable

Priority: P2.

## Violated invariant

`intro() as name` lets a proof choose the name of the variable it introduces,
where bare `intro()` takes the name the proposition was written with. It
should work wherever `intro()` introduces a variable.

It is refused on a range quantifier. For a goal `(lo..hi).all(|k| { ... })`,
`intro() as i;` fails with "`intro() as i` requires a goal written as
`forall (x: T) { ... }`; write `intro();` to keep the name this goal's
quantifier has". Bare `intro()` works on the same goal.

It is also untested on a `forall` over an algebraic type. The implementation
picks the reference form for the new name from the binder's type
(`universal_goal_renamed_for_intro` in
`src/surface/proof/proof_object/step_application.rs`), and only machine
integer, `Integer` and pointer binders have a test
(`mdtests/intro_as_names_the_introduced_variable.md`).

## Reproduction

```click
theorem range_goal(n: int32) {
    ensures (0..n).all(|k| { k == k }) by {
        intro() as i;
        intro();
        normalize();
    }
}
```

Fails with the message above. With `intro();` in place of `intro() as i;` it
verifies; the second `intro()` introduces the range guard.

## Intended change

A range quantifier keeps its binder in the lambda, not in a `forall` node, so
`universal_goal_renamed_for_intro` has no binder to respell. Rename the lambda
parameter and its uses in the body the way the `forall` case renames its
binder, with the same rule that the new name must not already be in scope.

## Intended regression

An mdtest with the theorem above, expecting `pass`, plus a theorem whose
later step reads the variable under its new name. A second mdtest, or a case
in `intro_as_names_the_introduced_variable.md`, for a `forall` over a
`spec enum` type.

## Acceptance

- Both regressions pass.
- `intro() as name` on a range quantifier whose chosen name is already in
  scope is refused with the existing "already in scope" message.
- The `intro() as name` row in `docs/reference/tactics/index.md` no longer
  lists the range quantifier as refused.
- `click expand` on a tactic after such an `intro() as` keeps the step and the
  result verifies.
