# A quantifier binder shadows a same-named C local in the kernel, capturing an unfolded predicate's argument

## Violated invariant

Substituting a predicate's arguments into its body must be capture-avoiding.
The surface does rename a quantifier binder that collides with an argument
name (`prepare_click_proposition_binding_body`,
`src/surface/lowering/contract_substitution.rs:468`), but it records the
original spelling in `written_name`, and `lower_for_all_proposition_to_spec`
(`src/surface/lowering/annotations.rs:3048`) passes that *display* name as
`SpecProposition::ForAllInt32 { name }`. The kernel then shadows the C local
of that name with the bound variable while lowering the body:
`lower_spec_universal_chain_in` (`src/kernel/spec.rs:756`,
`quantified_state.locals.set(name.clone(), integer_type.symbolic_value(*variable))`)
and the `ForAllMachineInteger | ForAllInt32` arm of
`lower_spec_proposition_at_state_with_algebraic_bindings_one_in`
(`src/kernel/spec.rs:1367`), with the same pattern for `ForAllPointer`
(`:1430`), `ExistsInt32`/`ExistsMachineInteger` (`:1571`) and
`ExistsPointer` (`:1632`). A substituted argument that lowered to
`SpecExpression::CExpression(CExpression::Variable("i"))` — a C parameter
named like the binder — is then read as the bound variable. `(0..n).all(|i|
..)` lowers to `ForAllInt32` with the written item name and is captured the
same way.

The surface already resolves every bound occurrence to
`SpecExpression::Value(symbolic)` through the elaboration environment, so the
kernel's `locals.set(name, ..)` is not needed for bound occurrences; its only
effect is to capture free C-local references of that spelling. The kernel
should bind quantifiers by `Variable`, never by source spelling.

## Reproduction

```c filename=repro.c
int32 f(int32 p[2], int32 i) {
    return i;
}
```

```click
verifying "repro.c";

predicate allpos(p: int32[], n: int32) {
    forall (i: int32) { 0 <= i and i < n implies p[i] > 0 }
}

int32 f(int32 p[2], int32 i) {
    views p[0..2];
    requires p[0] == 0;
    requires i == 2;
    ensures allpos(p, i);
} by {
    execute();
    unfold(allpos);
    simp();
}
```

Observed: `1 selected proof verified`, exit 0. `allpos(p, 2)` requires
`p[0] > 0`, but `p[0] == 0`. After unfolding, the argument `i` inside the
body is read as the bound `i`, so the body becomes `forall i. 0 <= i and
i < i implies ...`, which is vacuous.

Control: renaming the C parameter to `m` (`ensures allpos(p, m)` with
`requires m == 2`) is refused with `unclosed goal allpos(p, m)`.

The `(0..n).all(|j| { p[j] > 0 })` form with a parameter named `j`
also verifies
the same false claim, exit 0.

The pure-theorem form (`theorem t(p: int32[], i: int32) { ... ensures
allpos(p, i) by { unfold(allpos); simp(); } }`) is refused, because theorem
parameters are lowered to values rather than `CExpression::Variable` names;
the bug needs the C-function contract path, where parameter names stay
`CExpression::Variable` references that the kernel resolves against
`state.locals`.

## Intended regression

Both repro files above as `fail`-expected mdtests, plus a positive twin in
which the predicate is unfolded with an argument named like the binder and a
*true* claim (`requires p[0] > 0; requires p[1] > 0; requires i == 2; ensures
allpos(p, i)`) still passes, so the fix is a rename and not a refusal of the
spelling.

## Acceptance criteria

- The kernel never shadows a `CState` local by a quantifier's source spelling
  while lowering the quantifier body: the `locals.set`/`set_typed` calls at
  `src/kernel/spec.rs:756`, `:784`, `:1367`, `:1430`, `:1571`, `:1632` are
  removed or keyed by a name that cannot collide with a C local, and bound
  occurrences are resolved by the surface to the bound `Variable` only.
- Alternatively (defence in depth), `SpecProposition::ForAll*/Exists*` carry
  the fresh binder `name` for lowering and the written name for display only,
  and the kernel refuses a body that still mentions
  `CExpression::Variable(name)` for the binder's spelling.
- `ensures allpos(p, i)` in the repro is refused; the control and positive
  twin keep their outcomes.
