# Pointer-offset equality work is quadratic in the offsets' shared terms

Soundness: not soundness. The defect is the cost of a fast-part check; it
changes no fact, obligation, or verdict.

`pointer_offsets_equal_for_memory_resolution` in
`src/kernel/reasoning/memory_resolution.rs` decides whether two pointer
offsets in one block are equal. Memory resolution and `normalize() using`
both call it on their own input, so it is fast part: the
[verifier design](../docs/internals/verifier-design.md) rule allows work
proportional to the input, up to indexing factors. Its work instead grows
with the square of the number of offset terms the two sides share.

## Reproduction

The helpers of `mod index_sum_offset_tests` in
`src/kernel/proof/fact_reasoning.rs` build
`base + a1 + ... + ak + prefix + suffix` against `base + a1 + ... + ak +
total` at width 1, with the cited premise `to_integer(total) ==
to_integer(prefix) + to_integer(suffix)`. This test, placed in that module's
scaling file (`src/scaling_tests/kernel/proof/fact_reasoning/index_sum_offset_tests.rs`),
measures the general check on that goal:

```rust
#[test]
fn offset_equality_work_by_shared_terms() {
    let _session = VerificationSession::enter();
    let mut selected = PureFactContext::new();
    if let Proposition::ConditionIs(condition, value) = exact_sum() {
        selected = selected.assume_condition(condition, value);
    }
    for size in [4, 16, 64] {
        let Proposition::ConditionIs(ConditionTerm::PointerEqual(left, right), true) =
            address_goal(size, 1)
        else {
            unreachable!()
        };
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::reasoning::memory_resolution::pointer_offsets_proven_equal_for_memory_resolution(
                &left.offset, &right.offset, &selected,
            )
        });
        eprintln!("shared={size} work={work}");
    }
}
```

On master at 43fa3bf6 it reports 851, 4,560 and 48,456 work units for 4, 16
and 64 shared terms: 16x the terms costs 57x the work. The
index-sum rule that `normalize() using` tries after this check
(`offsets_equal_by_cited_index_sum`) costs 25, 73 and 265 on the same goals.
The work is in the general path, not the cancellation helper alone: the
element-index rebuild (`element_index_from_offset_with_facts`,
`element_index_rebuild_is_exact_for_width`) and the decisions over the rebuilt
sums run on terms the two sides share and could cancel first.
`cancel_common_offset_addends` in
`src/kernel/assumptions/condition_reasoning/order_paths.rs` is also quadratic
by itself (a linear search per addend), though its comparisons are not charged
as work.

Real proofs share one or two terms today (the Adler-32 trials do), so no
corpus proof is slow from this; it is a scaling-law violation found while
measuring that rule.

## Acceptance criteria

- The test above, turned into an assertion, shows work growing at most
  linearly (up to indexing factors) from 4 to 64 shared terms, for an equal
  pair and for an unequal one.
- Shared addends cancel before any rebuild or decision reads them, in linear
  time (a multiset count, as `offsets_equal_by_cited_index_sum` does).
- The memory-resolution and pointer scaling tests under
  `src/scaling_tests/kernel/` still pass.
