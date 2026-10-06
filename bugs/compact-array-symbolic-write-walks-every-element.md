# A symbolic scalar write walks every element of a compact local array

A single write at an unknown index must invalidate a compact array in work
proportional to its represented runs and cells, not its declared extent.
`CMemory::without_possible_aliasing_cells` instead visits the logical slots
of a constant run for an unconstrained symbolic offset. This violates the
scalable-verification requirement and can stall an otherwise compact proof.

## Reproduction

In a kernel unit test with a `VerificationSession` and the usual 8 MiB test
stack, build memory with two local blocks of `count * 4` bytes. Initialize the
source using `write_scalar_array_region(source, CType::UInt32, count,
CValue::UInt32(7u32.into()), false, false, &PureFactContext::new())`.
Optionally copy it to the second block and overwrite its last source lane;
those operations remain compact. Then call:

```rust
let unplaced = Pointer {
    block: source.block.clone(),
    offset: PointerOffsetTerm::scale_int32(
        Bitvector32Term::Variable(Variable(925_002)), 4),
};
let forgotten = memory.without_possible_aliasing_cells(
    &unplaced, 4, &PureFactContext::new());
```

Use counts 4, 1,024, and 1,000,000. The constructor-return investigation timed
the stages separately: initialization and ordinary copying took less than a
millisecond at a million lanes; invalidation took about 50 ms at 1,024 lanes
and about 52 seconds at a million lanes. The new aggregate-array copy itself
has a separate bounded scaling regression; this slow operation was in its
initial test-state setup and is not used by that copy.

Inspect `run_slots_kept_by_store` and the `SlotSet::PerSlot` / `AskWithin`
handling beneath `without_possible_aliasing_cells`. The unknown write must
forget potentially changed values while preserving the fact that previously
initialized bytes remain initialized. A known whole-array footprint already
invalidates compactly.

## Acceptance criteria

Add a regression covering an unconstrained symbolic index, and a constrained
index if it takes another path. Deterministic counters must include any slot
visits, so an accidental extent-sized walk cannot appear constant. Work must
stay bounded by represented memory size across the three counts above.
Preserve initialization, disjoint blocks and fields, and sound alias handling;
do not raise execution budgets or replace the symbolic write with a known
index in the regression.
