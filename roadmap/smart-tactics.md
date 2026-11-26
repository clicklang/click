# Smart tactics: fast checking and enforceable search boundaries

Soundness: incomplete. A cell named once by a selected program point and once
by its memory state gets two terms no rule relates, so a fact stated with one
does not prove a goal stated with the other: Click can refuse a true claim.
No false acceptance is known. Both open items below remove checking routes;
removing a route must keep ownership, aliasing, initialization, width,
lifetime and provenance refusals, and an unproved separation is never
permission to write or preserve a value.

## Goal

A simple checking operation costs its explicit input and necessary state
delta, up to indexing factors; ambient facts, owners, aliases, cached
observations and execution history must not make it slower. Discovery belongs
in budgeted, expandable search whose expanded steps obey the same rule. See
[Verifier design](../docs/internals/verifier-design.md) and
[Verification efficiency](../docs/internals/verification-efficiency.md); the
operation inventory, its scoped evidence and coverage gaps (R1, R2, F2, L1,
C1, J1, M1, E1, Q1), the prevention mechanisms, and the memory-history
checking boundaries are in its
[operation audit ledger](../docs/internals/verification-efficiency.md#operation-audit-ledger)
and [memory-history checking boundaries](../docs/internals/verification-efficiency.md#memory-history-checking-boundaries).
That ledger is not a defect list; this item tracks the two concrete open
pieces of work below.

## Program-point memory migration

Open item (a): delete the legacy memory-history walk.

Execution history supplies point identities and records the effects between
them; a read is named at a version point
([memory model](../docs/concepts/memory-model.md),
[point-named reads](../design/point-named-reads.md)). The legacy route instead
walks back from a memory state: `resource_tracker::last_same_version_point`
and the entries beside it (`last_same`, `last_same_named_cell`,
`cell_last_same_version_point`, `block_last_same_version_point` in
`src/kernel/resource_tracker/mod.rs`). Its production callers are
`cell_version_point` (`src/kernel/memory_history.rs`),
`array_ref_argument_point` (`src/kernel/spec.rs`),
`load_variable_for_cell_with_origin` (`src/kernel/eval/memory_loads.rs`),
`select_comparison_identity` (`src/kernel/eval/memory_loads/scalar_reads.rs`)
and `describe_unnamed_cell_addition` (`src/kernel/proof/execution.rs`), plus
the `last_same` callers.

The walk is deleted, not kept as a fallback. Two defects motivate it:

- **Quadratic naming.** For a cell no store wrote, the walk costs the stores
  into its block since the block's last version, so naming a fresh cell
  after each of `n` stores costs quadratic total work
  (`legacy_walk_naming_of_fresh_cells_still_grows_with_same_block_stores`,
  `src/scaling_tests/kernel/resource_tracker/tests.rs`).
  `known_legacy_fresh_reads_through_a_loaded_pointer_cost_the_same_at_every_position`
  (`step_shape_scaling_tests.rs`) is a step shape that still reaches it.
- **Mixed read naming.** A slice must move every producer of a read kind
  together, or a cell gets a point-named term and a memory-named term (see
  the Soundness paragraph). `crate::kernel::mixed_read_names::capture`
  reports each such cell the equality graph registers, with the line that
  built the memory-named read; the nightly
  `every_mdtest_reports_its_mixed_read_names`
  (`src/surface/tests/execution_tests.rs`) lists them over the mdtests.

`click audit legacy-walk` (`src/bin/click-audit/lowering.rs`, counting
through `kernel::resource_tracker::legacy_walk_audit`) counts the queries that
still reach the walk by calling site, resource and storage class; migrate
routes in order of that count, and run the mixed-read audit before and after
each slice.

Remaining slices, in recorded order (drop a step when it lands):

1. Recheck proof-only materialization against the point walk; repair any
   missing producer evidence.
2. Thread the caller's point through `materialize_composite_resource_memory`
   and `instantiate_composite_resource_body_resources`
   (`src/surface/proof/resources.rs`), using a setup root for standalone
   validation.
3. Attach initialized and uninitialized access-segment ranges to the entry
   root, keeping the definedness refusal.
4. Carry versions through straight-line effect batches, joins where both arms
   preserve the cell, calls with checked disjoint write footprints, and
   point-based loop views.
5. Carry an exact read's selected point through lowering, keys and raising;
   migrate other fixed-offset scalar reads (Booleans first; floats checked
   separately), then pointer and function-pointer reads with provenance,
   bounds and callability intact.
6. Extend address coverage to parameter and heap storage (fixed offsets
   first; symbolic offsets as a separate slice, with checked evidence naming
   the written storage), and reads assembled from bytes.
7. Migrate the remaining memory-state paths and remove each legacy route
   after its last production caller moves:

| Path | Remaining caller |
| --- | --- |
| Equality | `parameter_load` (`src/kernel/primitives.rs`) still produces projected-memory reads for abstract cells from bare memory producers or outside the verified entry path. |
| Observation | `canonical_cell_load` and `symbolic_load_value_unrecorded` (`src/kernel/eval/memory_loads.rs`) build memory-state observations for bare memory producers and unsupported indexed types or addresses. |
| Preservation | `array_ref_argument_point` uses the block walk for detached and uncertified views; the scalar naming walk calls it. `last_same_named_cell` follows recorded memory derivations for unsupported cells. |
| Raising | Detached array arguments use `synthesize_at_memory` (`src/surface/proof/surface_synthesis.rs`); detached scalar and abstract reads use `point_reading_load` (`src/surface.rs`). |

For each slice, test which point it selects, its raise/lower round trip, and
bounded work as unrelated history grows. Use `cell_version_on_path` only for
diagnostic comparisons in tests; production selection stays indexed. Keep the
[checking boundaries](../docs/internals/verification-efficiency.md#memory-history-checking-boundaries)
and their expansion/replay controls passing, and keep negative fixtures
reaching their intended refusals rather than prerequisite failures.

**Intended regression.** The two legacy-walk tests above flip: per-read work
stays within `O(log n)` of the history, so `n` fresh reads stay near
`n log n`, and the loaded-pointer shape no longer reaches the walk.

**Violated invariant.** A read is named by its version point alone; checking
does not scan execution history, and every producer of a read kind names it
the same way.

**Acceptance.** `last_same_version_point` and its sibling entries are
deleted; `click audit legacy-walk` has nothing to count and is removed with
the walk; `every_mdtest_reports_its_mixed_read_names` reports no cells;
ordinary fixtures and expansion/replay with implicit solving disabled pass
without changing C or weakening contracts.

## Transport retirement

The written tactic and its dispatcher have been removed. Regular proof tests
use `have`, `close()`, and explicit frame proofs. Remaining written sites
are outside the regular gate. The inventory below describes the original
migration scope.

The old `transport(source, target)` carried a fact across execution. Its
fixed-state route rebuilt transition contexts
with `assume_proposition_uncharged` (`count_uncharged_context_entries`
counts them), which grows with the path; see "Uncharged transport contexts"
in [verification efficiency](../docs/internals/verification-efficiency.md#output-sensitive-exceptions).
The replacement is explicit separation, `preserve(...)`, fact lookup,
rewriting and theorem application.

Written tactic sites (`.click` files, counted with a word-boundary match that
excludes names such as `plug_parent_consistent_transport`):

| Corpus | Files | Sites |
| --- | ---: | ---: |
| `examples/` | 5 | 22 |
| `library/` | 0 | 0 |
| `tests/` fixtures | 2 | 5 |
| `integrations/` | 2 | 9 |

`examples/` sites: `rbtree/rbtree-augmented/` 21 (in
`rbtree_size_rotate_model.click` 8, `rbtree_size_insert_mirrored_double_rotation.click`
11, `rbtree_size_insert_rotation.click` 1,
`rbtree_size_insert_mirrored_rotation.click` 1) and
`owned-vector/vector.click` 1. `rbtree-insert` and `rbtree-erase` have none.
Click fences in `mdtests/` hold 22 sites, mostly fixtures for transport
itself (`*_transport_expansion.md`, refusal and diagnostic tests); the
`c_named_contract_sequence_refinement_*` files declare a theorem named
`transport` and are not sites. `docs/concepts/own-project.md` has 1.
`design/` (60 sites in 13 files) is not counted.

Remaining chunks, one coherent PR each. Each migration verifies the whole
affected claim, expands and replays with implicit search disabled, and
rejects transport in the migrated family's output. A new primitive or a
verifier defect gets its own diagnosis rather than growing a chunk.

| ID | Work |
| --- | --- |
| 11 | Remaining loop-frame mdtests |
| 15 | Remaining fold, resource-observation and count mdtests |
| 24 | Augmented trees: basic rotation, model, propagation |
| 26 | Augmented trees: single and context rotations |
| 27 | Augmented trees: local double rotations |
| 28 | Augmented trees: context double and far rotations |
| 29 | Augmented trees: middle-subtree double rotations (split if large) |
| 30 | Reproduce residual internal producers' surviving transport output |
| 31 | Migrate producer paths chunk 30 demonstrates |
| 32 | Remove written syntax and dispatcher support, including `PostExecutionTactic::Transport` (`src/surface/proof/execution_state.rs`); update syntax tests and the mdtest fixtures above |
| 33 | Delete the transition-context rebuilding implementation |
| 34 | Enforce that an expanded proof cannot create `ProofSearch` (a test, not a text search) |

Producer anchors investigated in chunk 30:
`plan_explicit_universal_conclusion_discharge` and
`plan_explicit_loadability_transport`
(`src/surface/proof/surface_certificates.rs`), `try_carry_entry_conjunct`
(`src/surface/proof/smart_closures/search.rs`),
`fact_transport_candidate_search`
(`src/surface/proof/smart_execution/search.rs`), and the planned adapters in
`src/surface/proof/proof_object/execution_statements/search.rs`. A
constructor occurrence alone is not a surviving expansion.

Not confirmed as further generated-output families: computed or nested range
endpoints (`p[index + 1..length]`, `p[index..index + 1 + 1]`,
`p[index..index + 1u64]`) whose reduced probes failed under both plain and
restricted solve; bare same-state range `transport` missing its source-only
premise search; and `bound_universal_outcome_retains_instantiation_and_transport`,
which fails in `bubble_pass3` before expansion. Each needs a successful
expansion that retains transport before it becomes a chunk.

**Intended regression.** Chunk 34's boundary test, plus syntax tests that
expect written `transport` to be refused as unknown.

**Violated invariant.** Applying a proof step does not rebuild transition
contexts or search for premises; expanded proofs contain only ordinary
checked steps.

**Acceptance.** No written `transport` remains in `examples/`, `library/`,
`mdtests/`, `tests/` or docs; the parser, dispatcher, `PostExecutionTactic::Transport`
and the uncharged transition-context route are deleted; negative fixtures
keep their semantic refusals across proof contexts, and the boundary test
passes.
