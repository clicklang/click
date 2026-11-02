# Remove implicit memory-history searches from checking

Priority: P1.

## Remaining targets

**Pointer read naming: removal experiment, not ready to land.**
On `codex/pointer-read-naming-regression`, `CPointerValue::from_read` no longer
calls `resource_tracker::last_same_point`. It uses the supplied address and
snapshot's existing O(1) `unchanged_bytes_source()` link. That link identifies
cache-only observations of the same bytes; it does not cross actual writes.
`LoadedPointer`, its registry, initialization checks, and lifetime checks are
unchanged. Keep this separate from the pointer-representation work.

The regression `fresh_pointer_read_naming_across_store_history_has_near_linear_total_work`
in `src/scaling_tests/kernel/tests/memory_scaling_tests.rs` measures N fresh
pointer constructions after N disjoint stores. At N=16/32/64/128, baseline work
was 273/1057/4161/16513 (N² + N + 1); the experiment costs 16/32/64/128.
Same-cell and no-history controls also cost 16/32/64/128. Normal memoization
remains enabled, with no cache clearing between reads.

`mdtests/pointer_read_origin_explicit_transport.md` passes with the removal:
an explicit complete-pointer preservation certificate crosses a separated
write, and the preserved pointer can then be dereferenced. This establishes
one working case, not general recovery of all earlier provenance facts.

Remaining blockers in the experiment:

- The ordinary proof corpus has twelve failing fixtures (eleven formerly
  passing proofs and one changed expected-failure diagnostic). Copied aggregate
  parameter setup fails to connect its entry pointer facts to the contract.
  Removing redundant final rewrites only exposes the same certification failure;
  those exploratory proof edits were reverted. Other failures concern packed
  pointers, constructor evidence, and resource witnesses.
- Four focused kernel tests still fail: complete owned-store framing, cached
  pointer identity, recent pointer origin after havoc, and packed-word transport
  scaling. Preserve their assertions while investigating explicit evidence.
  The complete scaling suite reports 1144 passed and these three scaling
  failures out of 1147 tests; the owned-store framing failure is a unit test.
- `transport_framed_atomic_pointer_value` still calls `cell_version_point` for
  reconstructed complete words. Removing constructor cache warming exposes
  this traversal: one-write transport costs 288/336/528/1296 units with
  4/16/64/256 unrelated entries. Do not restore warming or raise the bound.

Next design review: determine how copied-parameter construction should record
its complete-pointer equality directly, and how packed-word transport should
use its supplied endpoints without finding an older designation. Discuss any
missing primitive before extending the kernel. Do not add a historical-source
fallback or weaken partial-overwrite, lifetime, or width checks.

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
