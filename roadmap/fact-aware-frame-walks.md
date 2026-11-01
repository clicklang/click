# Remove implicit memory-history searches from checking

Priority: P1.

## Remaining targets

First finish the cell-source removal candidate and its remaining
unit-test repairs listed in [Smart tactics](smart-tactics.md). Do not land it
with a smart proof that cannot replay.

The subsequent pointer-specific traversal in `pointer_read_value_recursive` and its frame
fallback still searches recorded memory history during ordinary checking.
`repeated_pointer_frame_queries_have_near_linear_total_work` in the combined
experiment (`codex/memory-walk-removal-current`) demonstrates quadratic total
work from repeated pointer-frame queries. Keep that regression with the pointer
removal; restricting the general cell-source lookup alone does not make it pass.

The general `memory_dag_cell_source` entry now inspects one transition. Its
bounded variants may reuse already memoized version summaries but must not
start a cold version walk. An inconclusive query is not preservation evidence.
Do not reintroduce source discovery to recover automatic proof coverage.

## Design and build cycle

For each remaining checking caller:

1. Isolate its history traversal with a deterministic scaling regression,
   including cold queries and misses.
2. State the needed preservation argument with explicit separation, a recorded
   statement `.footprint`, and `transport_certificate` links. Use the producer's
   typed reads and exact entry/exit snapshots. Do not reconstruct read identities
   or search for intermediate states while applying a link.
3. Remove the traversal and repair affected proofs without changing the C or
   weakening contracts. Discuss a missing primitive before extending the kernel.
4. Verify ordinary proofs and affected expansion/replay checks with the search
   disabled. Retain width, provenance, aliasing, partial-overwrite and freed-cell
   rejection controls.

Search that discovers these explicit links belongs in budgeted, expandable
planning. Applying a certificate must cost approximately its explicit size,
independent of unrelated history. A memo cache does not justify an unbounded
cold search in simple checking.

Coordinate this work with [Smart tactics](smart-tactics.md) and
[Spellability](../docs/internals/spellability.md). Keep the compact-run store
experiment separate. Do not replace these removals with a consolidated implicit
history search.
