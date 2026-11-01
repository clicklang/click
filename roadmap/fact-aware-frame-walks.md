# Remove implicit memory-history searches from checking

Priority: P1.

## Remaining targets

The `typed_read_has_same_memory_source` loop in
`src/kernel/memory_provenance.rs` supplies initialization checks through
`PureFactContext`'s read-definedness evidence. The ignored design regression
`repeated_read_initialization_queries_have_near_linear_total_work` calls
`has_memory_read_defined_evidence` after each unrelated store, retaining one
entry-snapshot premise. At 16/32/64/128 queries it charges
488/1744/6560/25408 work units. Adjacent-source controls charge
128/256/512/1024; exact-snapshot controls charge 32/64/128/256. Store construction
and premise admission are outside these query measurements. Run the red test
explicitly by name with `--run-ignored all`; it intentionally fails until removal.

Next design experiment: replace long implicit discovery with explicit transfers
of a selected `defined(...)` premise across individual separated effects.
First establish whether existing selected `transport` can supply a bounded
single-statement form, including bookkeeping transitions. If it cannot, discuss
a definedness-preservation certificate primitive before implementing it; current
certificate `preserve` produces observation equalities, not read-validity facts.
Value equality alone must never grant initialization or lifetime authority.
Keep type, alias, overwrite, havoc and allocation-retirement refusal controls.
The regression currently asserts successful legacy queries; the removal may
allow long implicit queries to decline while retaining positive adjacent and
explicit-proof controls.

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
