# Remove implicit memory-history searches from checking

Priority: P1.

## Remaining targets

The next target is `typed_reads_share_memory_source` in
`src/kernel/memory_provenance.rs`. Pointer value, designation, and extent
comparison reach it through `complete_pointer_reads_equal_across_frame` and
`pointer_reads_see_one_cell_source`. It alternates between the two selected
snapshots, following no-write predecessors until their histories meet.

`repeated_pointer_frame_queries_have_near_linear_total_work` in
`src/scaling_tests/kernel/tests/memory_scaling_tests.rs` measures 16, 32, 64,
and 128 stores with one entry-to-current check after each store. It retains
proved equalities and keeps caches live. Adjacent-state and explicit-composition
controls distinguish this hidden history discovery from explicit proof work.
The current local regression is red: entry-to-current work at those sizes is
21,423 / 72,991 / 266,751 / 1,016,767 units. Adjacent checks take
7,452 / 14,876 / 29,724 / 59,420 units; explicit composition takes
9,163 / 18,411 / 36,907 / 73,899. Retain both passing controls when removing
the implicit walk. The red test is isolated on `codex/pointer-history-next`;
do not publish it into the still-open cell-source removal PR.

The related `typed_read_has_same_memory_source` loop supplies initialization
checks through `PureFactContext`'s read-definedness evidence. Measure that caller
separately before including it in the same removal.

The general `memory_dag_cell_source` entry now inspects one transition. Its
bounded variants may reuse already memoized version summaries but must not
start a cold version walk. An inconclusive query is not preservation evidence.
Do not reintroduce source discovery to recover automatic proof coverage.

## Proposed next build

Design check
- Part: pointer equality and provenance comparison (fast memory checking).
- Why this part: ordinary condition and transport checks reach these helpers;
  expanding a surrounding tactic cannot eliminate their internal walk.
- Fast: retain indexed facts keyed by the selected typed pointer terms and
  exact read identities. Any implicit structural comparison may inspect only
  the two named snapshots and one immediate derivation per endpoint. Remove
  the growing predecessor search and reached-node sets. Do not replace them
  with alias enumeration or a second history fallback.
- Slow: no new search in this increment. Longer preservation arguments use
  existing `transport_certificate` `preserve` nodes over individual recorded
  footprints and `transitive` composition. If automatic discovery is later
  needed, it belongs in budgeted planning with this explicit expansion.
- Fact-stable: no change to read lowering or read identity; assumptions justify
  equality of existing terms rather than changing the terms produced.
- Failure: decline an unrecorded long-span equality; require explicit links.
  A miss proves neither inequality nor permission to ignore provenance.

Before landing, add long rejected-history controls (including pointer-half
writes), disable the walk, and repair the affected proofs with existing
primitives while retaining their C and contracts. Discuss any missing primitive
before extending the kernel. Measure initialization separately as noted above.

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
