# Remove implicit memory-history searches from checking

Priority: P1.

## Remaining targets

The `typed_read_has_same_memory_source` loop in
`src/kernel/memory_provenance.rs` supplies initialization checks through
`PureFactContext`'s read-definedness evidence. The local bounded experiment
on `codex/read-initialization-walk` accepts only identical snapshots or one
checked predecessor. At 16/32/64/128 repeated queries the cost falls from
488/1744/6560/25408 to 232/472/952/1912 work units. Adjacent and exact controls
remain linear. Long implicit queries now decline; preserving their former
automatic success is not required.

**Design blocker before landing:** even one C store may create a cache-forgetting
node followed by the actual store. The intended passing reproduction is
`mdtests/read_initialization_step_transport.md`: it starts with `defined(*p)`,
executes `*q = 1`, proves `separate(statement(0).footprint, memory(*p))`, and
explicitly selects both that separation and `at(before, defined(*p))` in
`transport`. The footprint premise succeeds, but the transport refuses because
the underlying memories are two internal edges apart. This fixture intentionally
remains red in the experimental checkpoint; do not publish the removal as ready.

Discuss a single-statement definedness primitive before continuing implementation:
from a selected typed defined-read fact at the recorded footprint's entry and
separation of the footprint from the read's complete range, construct the same
typed defined-read fact at its exit. Use the effect's recorded endpoints, not
ancestry reconstruction. Existing certificate `preserve` handles observation
equalities, not this definedness result. Value equality alone must never grant
initialization or lifetime authority. Keep type, alias, overwrite, havoc and
allocation-retirement refusal controls. After the primitive decision, repair
ordinary proofs, check expansion/replay, and run the full ordinary corpus before
landing. No new primitive or search fallback has been added in this experiment.

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
