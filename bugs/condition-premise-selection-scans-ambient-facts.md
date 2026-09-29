# Condition premise selection repeatedly scans ambient facts

## Violated invariant

One smart atomic derivation should spend work on condition facts relevant to
its goal, with bounded search over that relevant component. In
`src/surface/planning/proposition_search.rs`, `atomic_derivation_premises`
grows a connected condition component by walking `condition_fact_pairs()` in
a `while changed` loop. Each pass revisits all ambient conditions, and the
`selected.iter().any(...)` check grows with the selected set. An adversarial
fact order can require successive passes to discover a chain. This is a
planner cost, not a soundness failure or a reason to weaken the kernel's
condition checker.

The existing `condition_derivation_scales_near_linearly_with_unrelated_conditions`
regression in `src/surface/tests/scaling_tests.rs` covers a fixed two-premise
order derivation beside unrelated facts. It does not pin the cost of a longer
connected chain discovered across successive passes.

## Intended regression

Construct a fixed goal with a chain of relevant condition facts in reverse
iteration order, then grow both the chain length and a separate set of
unrelated condition facts over several deterministic input sizes. Measure the
complete smart derivation and its expansion and recheck; assert that the
certificate cites the needed chain, and include a negative case with a broken
link. Record work for candidate selection separately from kernel checking so
moving the scan into a helper does not hide it.

## Acceptance criteria

- Relevant condition premises are found regardless of insertion order, with
  no repeated whole-context walk per newly discovered chain link.
- Work is approximately linear, up to indexing factors, in the relevant
  component and emitted evidence; unrelated ambient conditions do not
  multiply that work. The multi-size regression pins this behavior.
- The resulting premise list is checked by the kernel and expands to a proof
  that independently re-verifies. Existing condition-reasoning reach is
  preserved, including load and snapshot terms.
- `scripts/check.sh` passes. This bug does not block e-graph migration unless
  a concrete migration slice hits this path.
