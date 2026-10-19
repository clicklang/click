# A written `simp` or `auto` after execution that closes nothing is skipped

## Violated invariant

`docs/reference/tactics/index.md`, "Goals after execution": a closer acts on
the first open goal and a refusal names that goal. A written `simp`,
`simp() using` or `auto` after execution in a per-claim proof that closes no
goal is instead skipped without a diagnostic. The implicit `auto` at the end
of the proof then closes the claim, and `click expand` drops the written
closer. A cited premise is never checked, so a false citation is accepted.

## Reproduction

`forall_scope.c`: `int32 forall_scope(void) { return 0; }`

```
verifying "forall_scope.c";
int32 forall_scope() {
    ensures result == 0 by {
        execute();
        simp() using { 1 == 2; }
    }
}
```

`click verify` reports the proof verified, and `click expand` at the `simp`
prints the proof without it.

The skip is the `if !require_explicit_closers { continue; }` at the end of
the `simp`/`auto` arm of `finish_ordered_proof`
(`src/surface/proof/claim_proofs.rs`). Removing it for written closers (keeping
it for the implicit closer, `source_index == usize::MAX`) refuses the proof
above. It also refuses two proofs that pass today only through the skip; fix
these first:

- `bugs/written-closers-miss-a-guarded-call-postcondition.md`
- `bugs/restricted-simp-after-execution-misses-the-returned-value.md`

## Intended regression

An mdtest with the proof above that expects failure naming the `simp() using`
tactic and the goal `result == 0`.

## Acceptance criteria

- A written `simp`, `simp() using` or `auto` after execution that closes no
  goal is refused with the goal it acted on and its checked context.
- The implicit closer still leaves an unclosed claim to the path-end report.
- After this, `simp` and `auto` on a proof `intro` opened read a miss
  against the goal list like the other closers (see "Goals after execution").
- The gate and nightly corpus show no other verdict change.
