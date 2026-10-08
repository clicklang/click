# Authority return-proof recheck scans the ambient context

## Violated invariant

A proof made of explicit simple tactics must verify in work proportional to
its own steps, not to unrelated facts in the proof context
(`docs/internals/verification-efficiency.md`). Under authority semantics,
completing a path that carries a retained return proof checks every fact of
that proof's base context, once per path. The work therefore grows with the
number of unrelated ambient facts.

## Reproduction

The library test
`surface::tests::scaling_tests::outcome_haves_and_resource_folds_do_not_reimport_ambient_facts`
passes under legacy semantics. Run it with authority semantics, for example
with the project's resource semantics set to authority. It then fails:

```
unrelated input facts changed the cost of the outcome operations:
[(8, 1, 1, 20), (16, 1, 1, 36), (32, 1, 1, 68), (64, 1, 1, 132), ...]
```

The last column is the number of materialized fact entries. It grows as
`4 + 2 * size` with the number of unrelated `requires x != i;` clauses, and is
flat across 1, 4 and 16 outcome operations.

## Cause

An outcome `unfold` under authority semantics is recorded on the completed
path through `ExecutionProofCore::record_return_transfer_wrapper_rewrite`.
That first flushes the pending return proofs, such as an outcome `have`, as
`CheckedExecutionEvent::ReturnProposition` events. `trace_completion` in
`src/kernel/proof/execution.rs` then checks the first retained return proof
with `retained.base.to_vec()`, which materializes the proof's whole base
context and checks each fact against the completion context. Later return
proofs only check `introduced_since` deltas. Legacy semantics never records
the unfold, so it never rechecks these proofs.

## Intended regression

Add an authority-mode copy of the scaling test above, or make that test run
under authority semantics once authority is the default. It must show the
materialized and indexed fact counts of the outcome operations independent
of the ambient requirement count.

## Acceptance criteria

- The first retained return proof on a path is checked against a kernel-held
  lineage of the facts at completion, through `introduced_since` or an
  equivalent delta. It is not checked by materializing the base context.
- The authority-mode scaling regression passes over at least four ambient
  sizes.
- `scripts/check.sh` passes.
