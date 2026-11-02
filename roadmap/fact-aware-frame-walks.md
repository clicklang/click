# Remove implicit memory-history searches from checking

Priority: P1.

## Remaining targets

Finish validation of the bounded read-initialization experiment on
`codex/read-initialization-walk`: ordinary corpus, affected examples, and
expansion/replay must pass before landing. The scalar store producer now folds
cache invalidation into its single `Store` edge. Keep its original input and
`ForgottenFrom` identity protection; do not reintroduce a standalone cache edge
or a history search to recover that input. The explicit one-store `defined`
transport has a regression in `mdtests/read_initialization_step_transport.md`.

**Pointer read naming needs a separate design cycle.**
`CPointerValue::from_read` calls `resource_tracker::last_same_point`, which
reaches `cell_last_same_version` and its history traversal. Naming program
pointer reads at the actual input snapshot, rather than a reduced cache view,
exposes this cost: the existing
`unfold_beside_descriptors_of_its_type_ignores_unrelated_descriptors` regression
measures 1266/1290/1386/1770 units at 4/16/64/256 descriptors in that experiment.
Keep the current scalar-read spelling fix separate from pointer naming. First
isolate this path with a cold repeated-query regression; discuss how an exact
typed read should acquire its designation and extent without searching history.
Do not simply drop provenance or width checks.

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
