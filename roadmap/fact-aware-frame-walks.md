# Remove implicit memory-history searches from checking

Priority: P1.

## Current branch boundary

`codex/pointer-read-naming-regression` is not ready to land. Keep its two
removals while repairing the remaining proofs:

- `CPointerValue::from_read` uses the supplied address and snapshot's O(1)
  `unchanged_bytes_source()` link instead of `resource_tracker::last_same_point`.
  The link crosses cache-only observations, not actual writes. Keep
  `LoadedPointer`, its registry, initialization, and lifetime checks separate
  from this work.
- Bounded cell-source checking does not consult `CELL_VERSION_MEMO`, and
  `MemoryDagHopJustification::SameVersion` is removed. Every retained hop
  corresponds to one actual transition. The history-naming cache still has
  other callers; their migration remains separate work.

Preserve `fresh_pointer_read_naming_across_store_history_has_near_linear_total_work`
and `bounded_cell_source_is_independent_of_history_cache`. Neither ordinary
memoization nor a warmed history cache may hide the cost of a cold query.

## Remaining proof repairs and validation

Three ordinary fixtures still fail:

- `cpp_generic_class_state_in_a_resource`
- `joined_pointer_field_read_rejects_different_field`
- `mutex_protected_pointer_footprint_stale_read_rejected`

The latter two fail before their intended refusal. Keep their expected errors
and repair the prerequisites. The mutex fixture stops at the first dereference
after locking, before the local assignment; preserving across that assignment
cannot repair it.

Three scaling cases remain red:

- `cached_pointer_reads_retain_their_current_cell_identity`
- `packed_word_transport_visits_only_the_selected_word_and_delta`
- `recent_pointer_read_origin_avoids_older_alias_histories`

The separate `cached_typed_pointer_read_emits_only_complete_owned_store_frames`
unit is also a known blocker. Keep its positive and negative assertions until
explicit replacement evidence is established.

The full scaling selection reports 1146/1149 passing. The ordinary corpus ran
4987 fixtures with the three failures above and one call-footprint regression;
the latter is repaired and all four `region_footprint` fixtures pass on rerun.
No full nightly run is required for this work. Rerun the ordinary corpus before
publishing once the remaining blockers are repaired.

## Preserve the explicit proof route

Use `transport_certificate` to preserve the complete pointer observation across
a separated transition. A numeric word equality alone does not connect pointer
provenance. The saved-word fixture uses `*(slot as (int32 **))` for its complete
eight-byte observation; it does not dereference the observed pointee.

Resource descriptors support `A * B` and `separation::emp`, with explicit
containment and separation laws in `click::separation`. A preserving call whose
mutable frame comes entirely from full-owned resource inputs publishes
`contains(bound, region.footprint)` when there are no additional effects.
Retain the checked caller-side resource identities, not the callee's equivalent
argument expressions. Keep recursive resources opaque and retain the concrete
memory-effect projection alongside the abstract bound.

Bounds for consumed inputs, non-unit quantities, construction, runtime effects,
and multi-transition regions are outside this initial form. Extend only when
a concrete proof needs them, retaining checked producer effects. Do not turn
arbitrary overlapping sequential effects into a separating conjunction.

Keep these expansion/replay checks passing:

- `saved_word_equality_expansion_cold_replay`
- `explicit_pointer_alias_repairs_expand_and_cold_replay`
- `recursive_witness_pointer_preservation_expands_and_cold_replays`
- `recursive_call_resource_bound_is_explicit_and_replays`

The recursive witness proof now selects the call's containment, applies
`separation::restrict`, and preserves the complete pointer read. It needs no
recursive resource unfolding or footprint reasoning in `normalize`.

## Next walks and invariants

`transport_framed_atomic_pointer_value` still calls `cell_version_point` for
reconstructed complete words. Its one-write work is 288/336/528/1296 for
4/16/64/256 unrelated entries. Do not restore constructor warming or raise the
bound. Search that discovers a path must emit preservation steps; warming a
memo is not a certificate.

Read-side `CellsForgotten` projections and bulk-write preparation remain
separate from scalar-store invalidation. Removing them requires preserving
read spelling and branch-scoped alias reasoning. `read_identity` is not
initialization/lifetime authority. Do not broaden changes into these paths
without a concrete reproduction and design review.

Keep complete-pointer equality and provenance comparison bounded to one
immediate predecessor per endpoint. Retain the repeated-query, adjacent-state,
explicit-composition, and cold-refusal controls in
`src/scaling_tests/kernel/tests/memory_scaling_tests.rs`. Cold histories include
writes to either pointer half; an undecided comparison must refuse equality.
Do not broaden artifact premise authorization into search or resurrect a
copy-evidence index. The copied-aggregate entry repair retains the producer's
exact complete-pointer equations.

## Design and build cycle

1. Isolate the next history traversal with a deterministic scaling regression,
   including cold queries and misses.
2. State the preservation argument with explicit separation, a recorded
   `.footprint`, and `transport_certificate` links. Use the producer's typed
   reads and exact snapshots; do not reconstruct identities or search for
   intermediate states while applying a link.
3. Discuss missing primitives before extending the kernel. Remove the walk
   and repair proofs without changing the C or weakening contracts.
4. Check ordinary proofs and expansion/replay with the search disabled. Keep
   width, provenance, aliasing, partial-overwrite, and freed-cell refusals.

Discovery belongs in budgeted, expandable planning. Applying a certificate
must cost approximately its explicit size, independent of unrelated history.
Coordinate with [Smart tactics](smart-tactics.md) and
[Spellability](../docs/internals/spellability.md). Keep the compact-run store
experiment separate.
