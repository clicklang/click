# Remove implicit memory-history searches from checking

Priority: P1.

## Remaining targets

**Pointer read naming: red regression ready for design review.**
`CPointerValue::from_read` calls `resource_tracker::last_same_point`, which
reaches `cell_last_same_version` and its history traversal. The constructor
already receives an exact read value, snapshot, and address; the walk selects
an older complete-read identity for its designation and opaque extent.

The local `codex/pointer-read-naming-regression` experiment adds
`fresh_pointer_read_naming_across_store_history_has_near_linear_total_work`
in `src/scaling_tests/kernel/tests/memory_scaling_tests.rs`. At N=16/32/64/128,
N fresh cells after N disjoint stores in the same object cost
273/1057/4161/16513 units: exactly N² + N + 1. Same-cell reads cost
18/34/66/130; fresh reads without history cost 17/33/65/129. All use normal
memoization, with a fresh verification session per size and no cache clearing
between reads. Store construction and exact read-identity creation are outside
the measurement. The intended near-linear assertion fails; both controls and
the existing-origin assertions pass. The regression remains local and red;
production code is unchanged.

Design question before removal: name the complete pointer's designation and
opaque extent directly from the supplied snapshot/address, then use explicit
complete-pointer preservation to relate it to an earlier read. Establish how
existing typed transport carries designation and bounds; numeric pointer equality
alone must not confer provenance or access. Discuss any missing primitive before
changing the constructor. Do not add a historical-source fallback or weaken
partial-overwrite, lifetime, or width checks.

Read-side `CellsForgotten` projections and bulk-write preparation remain
separate from scalar-store invalidation. Removing them requires preserving
read spelling and branch-scoped alias reasoning. `read_identity` is not
initialization/lifetime authority. Do not broaden the producer change into
these paths without a concrete reproduction and design review.

Keep complete-pointer equality and provenance comparison bounded to one
immediate predecessor per endpoint. Retain the repeated-query, adjacent-state,
explicit-composition and cold-refusal controls in
`src/scaling_tests/kernel/tests/memory_scaling_tests.rs`. Cold histories include
writes to either pointer half; an undecided comparison must refuse equality.

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
