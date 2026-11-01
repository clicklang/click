# Remove implicit memory-history searches from checking

Priority: P1.

## Remaining targets

The unlanded `typed_reads_share_memory_source` removal in
`src/kernel/memory_provenance.rs` replaces alternating ancestry discovery with
one immediate predecessor per endpoint. Complete-pointer equality, designation,
and extent comparison must retain that bound.

Before landing:

- Resolve the resource-descriptor spelling for a saved pointer base with
  current indices, needed by the arena store's separation proof. Reuse the
  existing `take`/`give` form if approved; do not add a history fallback.
- Finish the nested arena-prefix read preservation with explicit addresses,
  preserving the original C and produced range.
- Validate the full ordinary corpus and affected expansion/replay checks on
  the completed repairs. Keep this work separate from the open cell-source PR.

Retain the repeated-query, adjacent-state, explicit-composition, and cold
refusal controls in `src/scaling_tests/kernel/tests/memory_scaling_tests.rs`.
Cold histories include writes to either pointer half; an undecided comparison
must refuse equality. The ordinary repeated-query tests use 4, 8, 16, and 32
stores; cold-refusal tests include histories through 256 stores.

The related `typed_read_has_same_memory_source` loop supplies initialization
checks through `PureFactContext`'s read-definedness evidence. Measure that caller
separately before including it in the same removal.

The general `memory_dag_cell_source` entry now inspects one transition. Its
bounded variants may reuse already memoized version summaries but must not
start a cold version walk. An inconclusive query is not preservation evidence.
Do not reintroduce source discovery to recover automatic proof coverage.

## Removal design

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

Retain the rejected-history controls and discuss missing primitives before
extending the kernel. Measure initialization separately as noted above.

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
