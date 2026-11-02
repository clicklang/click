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

- The last full ordinary corpus run had six failing fixtures. Explicit full-
  pointer equality steps now make four pass in focused checks:
  `a_cast_contract_a_saved_word_keeps_its_historical_relationship`,
  `a_parent_cast_restated_after_a_store_lets_the_parent_be_dereferenced`,
  `rewrite_of_a_full_pointer_alias_keeps_constructor_type_evidence`, and
  `tagged_pointer_from_field_fact`. Only the parent-cast repair also passes
  expansion and cold replay; the other three remain blocked as described below.
  `c_decreases_resource_witness_child` and
  `call_through_witness_footprint_includes_its_memory` remain ordinary failures.
  The latter must reach its intended negative transport check, not merely fail
  earlier. No C or contract changes are part of these repairs.
- Four focused kernel tests still fail: complete owned-store framing, cached
  pointer identity, recent pointer origin after havoc, and packed-word transport
  scaling. Preserve their assertions while investigating explicit evidence.
  The complete scaling suite reports 1144 passed and these three scaling
  failures out of 1147 tests; the owned-store framing failure is a unit test.
- `transport_framed_atomic_pointer_value` still calls `cell_version_point` for
  reconstructed complete words. Removing constructor cache warming exposes
  this traversal: one-write transport costs 288/336/528/1296 units with
  4/16/64/256 unrelated entries. Do not restore warming or raise the bound.

**Immediate blocker: pointer equality proofs do not cold-replay.**
The focused `explicit_pointer_alias_repairs_expand_and_cold_replay` test in
`src/surface/tests/expansion_tests.rs` checks all four candidate repairs above.
It is a deliberately red investigation regression, run individually (7.2s),
not a full nightly run. Three fail:

- The saved-word proof's first `solve()` expands to `normalize() using {};`.
  Fresh verification rejects that step. The equality is between
  `((saved & ~1) as (struct node *))` and `p`; this happens before the source
  overwrite. Start the next reduction here.
- The constructor fixture's `unp == gparent` likewise expands to empty-premise
  normalization that does not cold-replay.
- The tagged-field fixture's `parent == next` expands to a failing
  `assumption()` after a preceding generated step.

The smaller `saved_word_equality_expansion_cold_replay` regression contains only
`unsigned long saved = *slot;`, an entry cast equality, and a `have` proving the
same cast of `saved`. No overwrite, dereference, resource witness, or struct
layout is required. It reproduces the saved-word failure in about 0.6s.

The hidden dependency is confirmed: a failed context-free normalization attempt
inside `solve` warms cell-version state. The later `normalize() using {};`
compares complete-pointer domains through `memory_dag_cell_source_with_stop`.
That one-transition query accepts `memoized_cell_last_same_point` and jumps from
snapshot 2 to snapshot 0. Fresh replay lacks the cached summary and refuses the
same goal. The goal's read coordinates agree across sessions; differing raw
`PointerLoadId`s were just session identities, not a lowering discrepancy.
Temporarily disabling only the memoized jump makes the original `solve` refuse
the goal instead of emitting the non-replayable certificate. Instrumentation
and the temporary disabling switch were removed after this experiment.

Next design/build: remove cache-dependent history jumps from simple read
checking; cached search results are not explicit proof steps. Then express the
copy's preservation argument through the existing primitive/certificate path,
checking whether the complete word's provenance can be carried by that path.
Do not count successful smart verification as a completed repair, restore the
naming walk, or warm the cache during replay. The parent-cast fixture is the
passing expansion/replay control. No production verifier change was made in
this investigation.

The witness experiments also remain unresolved. Naming the recursive witness
and explicitly proving the current cast equal to it succeeds, but the recursive
call still fails to match its owned `marked_list` resource. For the footprint
fixture, naming the witness and asking for the local pointer's equality fails;
the diagnostic says a selected pointer premise has no checked source spelling.
Those exploratory edits were reverted. Coordinate any necessary spelling change
with the separate spellability work; do not weaken the negative fixture's
expected refusal.

The kernel failures are not all timing failures. Cached pointer recovery and
recent call-havoc origin matching lose equalities previously supplied implicitly
by naming; complete owned-store framing also loses its expected equation. Keep
their positive and negative assertions until explicit replacement evidence is
established. Packed-word transport still succeeds but pays for unrelated older
history through `transport_framed_atomic_pointer_value`'s `cell_version_point`.
Its one-write work is 288/336/528/1296 for 4/16/64/256 unrelated entries.

**Entry setup: use the producer's complete-pointer equations.**
The empty-function copied-aggregate reproduction passes unchanged. Entry setup
was admitting alternate Surface pointer equations alongside the kernel entry
facts. Read-over-write closure derived another equality, which the later
artifact check then rejected as an additional input assumption. Both kernel
entry constructions agree; the setup fallback is not involved.

`contract_entry_view` now selects complete-pointer equations only by exact
membership in the kernel entry producer's existing fact set, then appends the
producer's other visible facts. Other source aliases retain their existing
selection: restricting those too exposes unrelated resource-range spelling
problems, which belong with the separate spellability work. This scoped repair
adds no equality search, history lookup, copy index, or pointer representation.
All eighteen aggregate-parameter fixtures pass after removing four redundant
final rewrites; C and contracts are unchanged. The selected kernel, scaling,
search-boundary, and aggregate expansion/replay checks report 1270/1273 passing,
with only the three known scaling failures above. The separate owned-store
framing unit still fails. The aggregate-parameter fact-stability audit reports
zero differences. Full ordinary corpus results are listed above. The tiny
`a_copied_aggregate_parameter_retains_its_pointee_requirement` fixture passes
unchanged. The false-entry-fact rejection guard passes. No nightly suite was run.

The corrected `logical_read_of_copied_pointer_retains_its_complete_value`
regression uses `contains_known` to test entailment; `proves_exact` tests premise
spelling. No additional copy-evidence index is needed for that case. The old
internal diagnostic's exact source spelling remains unestablished; this repair
does not change diagnostic rendering.

Remaining work stays with the failing automatic framing/recovery cases and
packed-word transport traversal above. Do not simply replace artifact premise
checks with a broader reasoner, or restore a historical-source fallback.

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

The general `memory_dag_cell_source` entry has a one-transition bound, but its
bounded walker still reuses memoized version summaries. The replay regression
above shows why this exception must be removed: a warm summary changes what a
simple step proves. An inconclusive query is not preservation evidence.
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
