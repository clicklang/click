# Unspellable facts: make every proof-state fact round-trip

Priority: P1.

Soundness: incomplete. Every cited spelling is lowered again and checked, so
no false acceptance is known. A fact with no spelling costs completeness (a
smart tactic declines a route whose premise it cannot cite), expansion
(`click expand` cannot write the step out) and readable reports
(placeholders such as `<unnamed A>`).

This is a handoff document for the work in progress. The rule itself, and
the tools that measure it, are in [Spellability](../docs/internals/spellability.md);
read that first.

## The goal

For every kernel term a proof state holds, `lower(raise(x)) == x`. That needs
two things:

1. **Lowering is structural and fact-stable.** A lowered term has the
   structure of its surface text. Facts may decide whether lowering succeeds
   and add side facts, but they never choose the term. Equalities live in
   the equality graph and the comparison form, which every check consults.
2. **Every kernel term and fact kind has a Surface spelling.** A value is
   named where it is introduced (a call result, a havoc, an allocation), and
   every fact kind has syntax.

## Decisions already made by the user

- Make lowerings structural in small PRs. Ask only when a step needs a
  decision, not about ordering.
- `A implies B` and `A or B` guard the right side's definedness
  obligations: `A implies obl`, `A or obl`. Kernel `/` by zero is an opaque
  total term. A Click `/` that returns an option is a possible future
  change, owned by the integer thread.
- Fact-dependent integer lowerings belong to the integer thread, recorded in
  [standard-library.md](standard-library.md#fact-dependent-integer-lowerings):
  spec `/` and `%`, `byte_stride_index` and `pointer_index_term`.
- The empty population is handled by a real kernel axiom,
  `population_member_count_zero`: `count(R(a, _)) == 0` implies
  `count(R(a, k)) == 0`. The user accepted this to keep the work moving.
- A call's result is spelled `<region>.result`, beside the region's
  `entry` and `exit` points. It is not a magic `result` word inside `at(...)`.
- **Stepping must stay near linear.** A proof may take n² work, but stepping
  through a function of n statements must not. Adding to the equality graph
  during a step is fine when finding the addition is cheap: no work that
  repeats per step over the whole history.
- **Prefer one-step frame decisions.** Each step decides what it keeps,
  looking one step back with the facts it has. Don't walk back n steps for
  every query. A proof restates a frame that needs a fact learned only
  later.

## Landed

- Structural lowerings for membership disjunction, null-pointer class
  evidence, `count(reference)` anchors, the empty range fold, wildcard
  population members, a zero pointer offset, `held(m)`, and `or`/`implies`
  obligations.
- The population axiom, and the `old(count(R(a, k)))` spelling of an exact
  member's entry count.
- `<region>.result`, with call results spelled by their call in traces,
  ranges and unwound reports.
- An entry-snapshot resource argument is read as written, with no fact
  search.
- Frame walks (see [fact-aware-frame-walks.md](fact-aware-frame-walks.md)):
  - the fact-aware cell walk resumes the memoized version walk;
  - C program reads (`cell_value_on_path`) go through that one walk.

## In progress: pointer reads named by version

The largest remaining known violation, listed in
[Spellability](../docs/internals/spellability.md#lowering-is-structural): a
logical pointer read lowers to the pointer stored in its cell, through the
fact-consulting fold `memory_provenance::complete_pointer_read_value` and the
stored-pointer fold in `Pointer::loaded`. So `p->next` after `p->next = q`
lowers to `q`, and `lower(raise(x)) == x` fails.

**Branch.** The work in progress is on `claude/pointer-reads-wip`. It has
15 checkpoint commits, about +680/−60 lines across 17 files, and was rebased
onto master after the frame-walk PRs. Expect to cut it into small PRs; it
should not land as one piece.

**What it does:**

- **Version names.** A logical read of a pointer cell lowers to the read at
  the cell's version (`logical_read_names_its_version` includes pointers;
  `CMemory::symbolic_pointer_version_load`; `Pointer::version_read`).
- **Pointer read-over-write authority.** `pointer_read_over_write_value`
  answers with the pointer the read's snapshot stores at its address, when
  the fact-free version walk shows it (`memory_shown_cell_value`). That
  answer is memoized per snapshot. It refuses a cell that only a fact kept.
  It is used in:
  - comparison forms, for `PointerEqual` and `PointerValueEqual`;
  - equality-graph registration, as term metadata
    (`register_logical_read_values`);
  - block distinctness (`loaded_pointer_stored_block`).
- **Addresses offset from a read.** An address offset from a pointer read
  reaches its stored cell through the stored pointer
  (`stored_pointer_address`). It is used by the integer read-over-write
  authority, and by the exact-address lookup for values that don't name
  their version, such as generic `T`.
- **Rewriting** moves through pointer reads (`equality_rewrite.rs`,
  `term_rewrite.rs`).
- **Tests.** The unit tests that pinned the fold are updated, and there is a
  new mdtest, `a_read_of_a_stored_pointer_cell_stays_a_read.md`.

**Original checkpoint status.** The unit phase had the 15 failures below.
Its fixture phase had not run because the gate stopped after the unit phase.
See the integration checkpoint below for subsequent results.

- **Nine Rust/Charon tests:**
  - `charon_box_fields_take_and_assign_through_self`
  - `charon_generic_container_refuses_a_stronger_put_and_a_false_caller`
  - `charon_generic_container_verifies_through_a_dyn_container`
  - `charon_generic_stack_verifies_once_for_every_type`
  - `charon_recursive_drop_frees_every_node`
  - `charon_recursive_drop_glue_needs_ownership_and_a_measure`
  - `charon_stack_refuses_false_push_pop_and_round_trip_claims`
  - `trait_objects::charon_inline_match_over_a_held_resource_field_refines_itself`
  - `trait_objects::charon_trait_functions_are_defined_from_a_held_resource`

  Most report either "return resource observation has a different checked
  exchange" or a `fold` that cannot establish a body fact. `Stack::push`
  in `design/charon-trial/generic-stack` verifies; `pop` fails at its
  second `fold`.
- **Six unit tests** that pin the old stored-value behavior:
  - `memory_loads::tests::a_symbolic_pointer_read_recovers_the_complete_stored_value`
  - `memory_loads::tests::forced_logical_pointer_reads_keep_the_snapshot_identity_of_cached_values`
  - `memory_loads::tests::scaling_tests::cached_pointer_reads_retain_their_current_cell_identity`
  - `memory_loads::tests::unknown_pointer_in_fresh_storage_does_not_inherit_storage_provenance`
  - `retained_aggregate_resource_values_tests::scaling_tests::retained_resource_fields_preserve_lvalues_and_scale_with_expression`
  - `statement_steps::explicit_transport_keeps_evaluated_tagged_pointer_sources_after_a_join`

  Each needs checking: either the expectation moves to "the read keeps its
  name, and the authority relates it", or it is a real loss.

**Why the Rust tests fail: frames the old fold supplied silently.**
Take `pop`:

```rust
let node = self.head.take()?;
self.head = node.next;
// ...
free(node);
```

At exit, `self.head` is a version name. To match the owned
`allocation(p)` and `*p`, a check must relate it to the pointer stored by
`self.head = node.next`, which means crossing `free(node)`. Memory alone
cannot show the freed block (a pointer read) separate from `self`. The old
fold crossed it through facts inside lowering.

A separate import defect obscured a diagnostic probe: Rust record pointer
fields lost their nominal pointee name, so `self.head.next` fell back to an
untyped load at offset zero instead of the declared eight-byte pointer field
at offset eight. Comparing `self.head` with `old(self.head.next)` then paired
a pointer with `int32`; the rejected comparison reported only "0 paths".
Retaining the field's pointee layout restores the typed nested read. Rejected
specification comparisons now retain their operand types and operator for
the proof diagnostic. This fixes the probe's lowering, not the remaining
nested frame equality.

Two shared read-definition prerequisites are now covered independently of the
pointer-read migration. Direct pointer-read names retain their producer-recorded
projection edges in the equality graph, just as scalar-backed names do. A
successful resource fold/unfold also retains its child reads' checked definitions
in the caller's graph; previously they stayed in a temporary opening context.
A refused exchange publishes none. These are internal read definitions, not
new public proof-state facts. Both changes avoid fact-aware query fallbacks and
have deterministic scaling coverage for selected chains and unrelated state.

### Integration checkpoint (2026-10-27)

The migration is continued on `codex/unspellable-free-investigation`, rebased
onto `14aa465dd` (including the importer fix #2065 and read-definition fix
#2073). The owned free-frame prototype remains on that branch; its frame
facts are checked consequences of the free, not unconditional metadata.

PR #2075 (`c4a8153a6`) moves the published return resource exchange inside
the kernel operation and returns its constructed state and facts. The
follow-up uses the retained C-body successor during final return certification
instead of comparing it with a regenerated representation. Existing path
premise checks still run; this does not remove all legacy trace replay.

Abstract-value reads now participate in typed address congruence. Their
pointer operands register through the common graph walk, and exact producer
projection edges connect their snapshot names. Structural read naming also
retains the original observation as a width-specific definition: naming had
already justified that relation but discarded the original snapshot. The
new graph edges change no lowered terms, scan no facts or memory history,
and never cross an actual affecting store or mix read types or access widths.

With these increments and the WIP full-pointer substitution correction, the
unchanged generic Stack proof verifies end to end, including `push` and
`pop`. Focused regressions check late aliases, nested pointer definitions,
projection/origin relations, type and width separation, writes, and fact
withdrawal. Deterministic scaling covers 8/16/32/64 reads and up to 256
unrelated facts. The complete migration still needs a green gate and the
remaining spellability/fact-stability acceptance work below.


The integrated migration unit gate ran 6,620 tests: 6,609 passed and 11
failed (five Rust container/drop tests and the six representation tests
listed above). Box fields, generic Stack, and both held-resource trait tests
now pass. The false-Stack-claims test still refuses verification, but earlier
than its expected diagnostic at a concrete `Stack::pop` payload fold.

The separately invoked fixture phase passed the C++ and sidecar aggregates.
Eight examples failed: `arena`, `binary-tree`, `concurrency-fork-join`,
`input-cursor`, `owned-segmented-buffer`, `owned-string`, `owned-vector`, and
`perpetual-service`. The main mdtests reported nine failures and then remained
in `rewrite_through_a_loaded_pointer_field.md`; that process was stopped
at 416 seconds after all other main fixtures had finished. This is an
unresolved migration tooling blocker, not a completed fixture verdict.
The obsolete `execute()` in `a_read_of_a_stored_pointer_cell_stays_a_read.md`
was subsequently replaced by `step_until(function.exit)` and passed in a
focused rerun. The eight other reported failures are:

- `aggregate_parameter_old_pointee.md`
- `aggregate_parameter_pointee_expires.md`
- `aggregate_parameter_pointee_contract.md`
- `aggregate_parameter_pointee_resource.md`
- `an_entry_view_names_the_entry_address.md`
- `authority_ordinary_exit_aggregate_parameter_pointee.md`
- `c_produced_resource_over_returned_struct_field.md`
- `cpp_generic_class_state_in_a_resource.md`

The isolated abstract-read follow-up passed `scripts/check.sh`: 6,620
unit/API/import/scaling tests and all four fixture aggregates (13m41s,
report-only ten-minute budget warning). The loaded-pointer fixture passed
in 0.27 seconds there; the stall is reproduced on the broader migration.

The loaded-pointer stall was reduced to a same-thread equality-graph deadlock:
read-definition registration called `last_same_named_cell`, which re-ran the
stop's effect check and attempted to lock that same graph. Retaining the stop
reason alongside the existing `(snapshot, address, width)` version memo fixes
the stall without changing the endpoint or the checked proof. The original
fixture passed in 0.68 seconds; all 56 focused tracker/fixture tests passed.
The new regressions check that later graph growth does not reclassify the
retained decision, and measure 8/16/32/64 new steps plus 0/16/64/256 unrelated
names. A focused before/after fact-stability audit of the stored-pointer
fixture passed with zero differences. The isolated full `scripts/check.sh` passed all 6,622 unit/API/import/scaling
tests and all four fixture aggregates in 15m53s (report-only budget warning;
a separate migration diagnostic build ran concurrently).
No nightly suite was run; the full migration acceptance audits remain open.

### Decision: the free decides its frame from proven separation

The user chose the executor to require separation, with the step recording
ownership-supported before/after read equalities in the equality graph.
The process must be deterministic and indexed, looking one step back; no
history scan per query and no fact-aware fallback inside individual checks.

The investigation found a stale cache entry, but no false verification:

- A helper returning `p + 2` for an `int32*` gives an interior alias eight
  bytes into the allocation. Reading through it before `free(p)` verifies;
  reading after the free is refused for missing read authority. See
  `an_interior_call_alias_can_be_read_before_free.md` and
  `an_interior_call_alias_cannot_be_read_after_free.md` in `mdtests/`.
- The kernel reproduction `free_retires_a_cached_interior_alias` showed that
  `free_heap_block` nevertheless kept a cached value under a symbolic
  `q == p + 8` spelling. The same-offset test in
  `heap_allocation_may_contain_pointer` did not identify this interior alias.
  Cache retention therefore cannot be used as the walk's separation rule.

The first increment requires complete-cell ownership in the checked residual
frame before keeping an uncertain cached cell. The step has already consumed
the allocation’s complete ownership and checked the resources that survive;
its residual owners are separate from the consumed bytes by construction.
`owned_memory_member_covering_access` selects a cell’s owner through the
address-class access index. Unknown cells are forgotten; structurally distinct
blocks remain untouched. The allocation-status helper is not a separation
authority.

The migration checkpoint records supported pointer-cell frame equalities at
the free step, with deterministic full-step scaling coverage. That increment
has not landed; remaining container and concrete recursive-drop failures must
be resolved before the pointer-read migration is green.

### Also tried, and why it was dropped

- **A fallback in each check.** `pointers_proven_equal_for_memory_resolution`
  resolved a read through the fact-aware walk. It made `allocation(self.head)`
  match, but only because it used the cache of a snapshot where the walk
  stopped at an edge it could not cross. The codebase deliberately refuses
  that: see the comments in `checked_pointer_read_endpoint_and_kind` and
  `graph_for_memory_query` about weakened contexts. A fallback in each check
  is also the scattering that
  [fact-aware-frame-walks.md](fact-aware-frame-walks.md) forbids.
- **Frames written in the proof.** `have self.head == at(region(120).exit,
  self.head)` closes the allocation. The follow-up
  `have self.head.next == at(region(120).exit, self.head.next)` does not
  close by `solve`.

## Other remaining work

- **Known fact-dependent lowerings** (see
  [Spellability](../docs/internals/spellability.md#lowering-is-fact-stable)):
  comparisons folded to constants, decided guards and disjuncts dropped, and
  comparison kinds chosen by known provenance. `CLICK_FACT_STABILITY=<path>`
  with `scripts/fact-stability.sh` lists the current ones over the mdtest
  corpus.
- **Naming at introduction.** Call results are done. Havoc values,
  allocations, and states between recorded points still print as
  placeholders in some reports. `scripts/spellability-census.sh` finds them.
- **Syntax for missing fact kinds.** Writability, and the memory a step may
  change (the census "no syntax" gap).
- **The total speller.** Replace the premise speller's search and its
  fallbacks with spelling by construction (the census "writable but not
  found" gap).
- **Enforcement.**
  - A census ratchet: the count of written-step misses may only fall.
  - A test-build assertion that `lower(raise(x)) == x` holds for every fact
    a checked step adds.

## Acceptance criteria

- `complete_pointer_read_value` and the stored-pointer fold in
  `Pointer::loaded` are deleted. The generic-stack, generic-container,
  recursive-drop and trait-object Charon fixtures verify unchanged, or with
  frame steps the user accepts.
- `scripts/fact-stability.sh` reports no differences.
- The spellability census reports no misses for written steps, and a
  ratchet test keeps it there.
- A test-build assertion checks `lower(raise(x)) == x` on every fact a
  checked step adds.
- No stepping scaling regression: the frame work above keeps stepping
  linear in the number of statements.
