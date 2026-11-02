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

**Current checker boundary and proof repair.**
Bounded cell-source checking no longer consults `CELL_VERSION_MEMO`. The cached
lookup helper and `MemoryDagHopJustification::SameVersion` are removed. Each
retained hop now corresponds to one actual transition. The history-naming cache
still exists for other callers; its removal/migration remains separate work.
`bounded_cell_source_is_independent_of_history_cache` checks the same query
before and after warming the history cache at 2/8/32 preceding stores. It failed
before this change and passes afterward.

`mdtests/saved_word_explicit_transport.md` supplies a working explicit argument:
separate the local declaration's footprint from the source word, then preserve
the complete eight-byte observation through `*(slot as (int32 **))`. The
pointer-typed view connects provenance; a numeric word equality alone does not.
No pointee is dereferenced by this observation. Assignment then copies the
preserved value. The original saved-word overwrite fixture uses the same
argument without changing its C or contract.
`saved_word_equality_expansion_cold_replay` checks both explicit proofs and their
fresh expanded replay, and checks that the old cache-dependent `solve` refuses.
Both tests pass; the saved-word lowering audit reports zero differences.

**Remaining validation and blockers.**
The kernel, transport-certificate, memory-DAG, resource-tracker, and full scaling
selection reports 1284/1287 passing. The three failures are the already known
cached-pointer identity, recent pointer origin after havoc, and packed-word
transport scaling cases. The separate complete owned-store framing unit also
remains a known blocker. Keep their positive and negative assertions until
explicit replacement evidence is established.

The last full ordinary corpus run reported 4970 passing fixtures and nine
failures. Subsequent focused repairs use explicit complete-observation
preservation, leaving these known ordinary failures:

- `cpp_generic_class_state_in_a_resource`
- `joined_pointer_field_read_rejects_different_field`
- `mutex_protected_pointer_footprint_stale_read_rejected`

The latter two are negative fixtures that fail before their intended refusal.
Keep their expected errors; repair the prerequisites. The mutex fixture stops
at the first dereference after locking, before the local assignment, so
preservation across that assignment cannot repair it.

`explicit_pointer_alias_repairs_expand_and_cold_replay` covers the saved-word,
parent-cast, constructor-equality, tagged-field, call-preserved integer address,
and interface-resource argument repairs. The interface case preserves both the
parent pointer field and its child's pointer field across a local assignment.
The negative call-through-witness fixture now reaches its intended transport
refusal after complete-observation preservation. No C or contract changes are
needed for these repairs.

**Next design question: recursive-call footprints.**
`c_decreases_resource_witness_child` passes ordinary verification with explicit
preservation across the local declaration. Its expansion still fails replay at
the final fold's pointer equality. The ignored red regression
`recursive_witness_pointer_preservation_expands_and_cold_replays` retains that
mismatch; do not count this proof as repaired until replay passes.

The explicit missing link is preservation of `node->word` across the recursive
call. Before the call, `separate(marked_list(child), memory(node->word))` is
provable. Afterward, normalization with that separation and the explicit
call-argument equality cannot prove
`separate(statement(1).region(1).footprint, memory(node->word))`.
`OwnedFootprintDerivation` in `src/kernel/functions.rs` deliberately represents recursive
resources with `CMemoryRange::unnamed_footprint()`. The execution-produced region
footprint copies this anonymous memory range from `CMemoryEffectSummary`; it
cannot connect it to the selected resource separation. The call retains the
caller frame, but the explicit footprint rule lacks the resource identity.
Discuss preserving the call's resource-level effect evidence before extending
the kernel. Do not unfold recursive resources into a memory search or restore
history-cache jumps to bridge this gap.

All six edited ordinary fixtures pass focused verification. The six-case
repair expansion/replay group passes; the separate recursive replay regression
is red. The lowering audit over the six edited fixtures reports zero
differences. No full corpus or nightly suite was rerun for these proof repairs.

`transport_framed_atomic_pointer_value` still calls `cell_version_point` for
reconstructed complete words. Its one-write work is 288/336/528/1296 for
4/16/64/256 unrelated entries. Do not restore constructor warming or raise the
bound. Search that discovers a path must emit the preservation steps; warming a
memo is not a certificate.

The branch's copied-aggregate entry repair retains the kernel producer's exact
complete-pointer equations, avoiding additional derived entry assumptions.
Other source aliases retain their existing selection. Do not broaden artifact
premise authorization into search or resurrect a copy-evidence index.

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

The general `memory_dag_cell_source` entry inspects one transition. Its bounded
variants obey their explicit transition limits regardless of history-cache
contents. An inconclusive query is not preservation evidence. Do not reintroduce
source discovery to recover automatic proof coverage.

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
