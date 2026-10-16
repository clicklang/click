# A load frame walks each snapshot to its oldest recorded history

Soundness: sound. Only the cost is wrong: every answer is unchanged, but the
work of one checked load equality grows with unrelated history recorded before
both snapshots, which the [verification efficiency
contract](../docs/internals/verification-efficiency.md) forbids for simple
checking.

## Violated invariant

Deciding that one cell reads the same at two snapshots must cost work bounded
by the steps between them (plus indexing), not by the history either snapshot
has behind it. The question
`explicit_atomic_equality_from_memory_derivations(load(before, p),
load(after, p))`, where `after` is `before` plus one store elsewhere, costs
about 6 units per unrelated store recorded before `before`.

The work goes to `LoadCellWalks::run` (`src/kernel/memory_provenance.rs`,
reached through `atomic_loads_equal_along_memory_derivations` ->
`recorded_load_history` -> `recorded_load_history_uncached`). It runs
`memory_dag_cell_source_with_stop`
(`src/kernel/resource_tracker/cell_source.rs`,
`memory_dag_cell_source_walk_inner`) once per side. Each walk continues to the
oldest recorded snapshot (`CellWalkStop::OldestRecorded`), at about 3 units per
hop: one hop plus the `step_effect::affects` classification. Neither walk stops
at the other side's snapshot, although `after`'s walk passes through `before`
after one hop and the two loads are then the same node. The definedness frame
(`typed_read_has_same_memory_source`) stops at the named source and stays
flat. This is the walk the quantified frame's value leaf (`loads_unchanged`)
and the single-fact transport both use.

## Reproduction

A kernel unit test. `before` is a 16-byte block plus an unrelated block holding
N earlier one-byte stores. `after` is `before` with `uint8 0` stored at offset
8. Both snapshots are interned, and the queried load is `uint8` at offset 0.
The work is the deterministic work of the first (uncached) query in an empty
`PureFactContext`:

| N unrelated earlier stores | left walk | right walk | `explicit_atomic_equality_from_memory_derivations` |
|---|---|---|---|
| 16  | 49  | 50  | 103   |
| 64  | 193 | 194 | 391   |
| 256 | 769 | 770 | 1,543 |

The probe was the test
`definedness_frame_is_flat_against_unrelated_history_and_facts` in
`src/scaling_tests/kernel/quantified_frame/definedness_frame_tests.rs`
(from the fix for the guarded-definedness frame), with the value leaf measured
by these calls:

```rust
let bi = crate::kernel::intern_c_memory_ref(&before);
let ai = crate::kernel::intern_c_memory_ref(&after);
let load = |m: &SharedCMemory| Bitvector32Term::MemoryLoad(
    m.clone(), Box::new(base.clone()), LoadKind::UInt8);
measure_deterministic_work(|| memory_dag_cell_source(&bi, &base, 1, &empty, true));
measure_deterministic_work(|| memory_dag_cell_source(&ai, &base, 1, &empty, true));
measure_deterministic_work(|| explicit_atomic_equality_from_memory_derivations(
    &load(&bi), &load(&ai), &empty));
```

In a program, this is `memset(dst, 7, 4); dst[4] = 0;` preceded by N unrelated
stores, with the guarded `memset` postcondition carried across `dst[4] = 0`.

## Acceptance criteria

- A scaling regression beside the existing one runs the three sizes above.
  It asserts that the first query's work for the load equality across one
  disjoint store is equal at 16, 64 and 256 unrelated earlier stores, and that
  it grows with the steps between the two snapshots, not the steps before them.
- Answers are unchanged: the existing refusal regressions still refuse, for
  example `mdtests/a_guarded_memset_postcondition_does_not_cross_a_store_in_its_range.md`
  and the `quantified_frame_rejects_*` family. This includes the case where the
  cell was last written before `before`, and the stored-value pinning arm.
