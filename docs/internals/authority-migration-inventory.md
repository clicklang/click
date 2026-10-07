# Authority migration: consumer inventory

This is the consumer inventory and migration record for `issues/authority-migration.md`. It is not a specification of new syntax. The issue holds the plan; this page records which consumers remain on the legacy resource/population rules, which have migrated, and the evidence collected as each group landed. Design notes are proposals or historical investigations, not passing fixtures. The C in source-backed fixtures is frozen by the migration issue.

## Current status

Milestones 1–4 of the migration issue are complete. The sequential refcount project, the shared-parent design project, the bounded-pool project, every sequential mdtest population consumer, and every mutex count fixture without workers select authority semantics. The remaining legacy consumers are listed in the next section:

- 21 count fixtures in the worker groups (milestone 6);
- 2 `guarded_by` fixtures, both in the worker protected-memory group, which migrate in milestone 6;
- `fold_negative_quantity_legacy_control.md`, a deliberate legacy control retired in milestone 7 against its authority replacement `fold_rejects_a_negative_quantity.md`.

Remaining `count(` search hits outside these groups are C functions named `count` or the standard library's array `count(p, lo, hi, x)`; none observes a declared-resource population.

## Remaining legacy groups

These fixtures use the legacy path. The two worker families are intentionally separate: ordinary abstract accounting does not prove a protected C counter equality. The issue assigns the `guarded_by` group to milestone 5 and the worker groups, including the two worker fixtures with protected memory, to milestone 6.

| Group | Files and preserved behavior |
| --- | --- |
| Abstract workers and joins | `modeled_pthread_counted_join.md`, `modeled_pthread_counted_reverse_join.md`, `modeled_pthread_counted_before_join.md`, `modeled_pthread_counted_join_stale.md`, `modeled_pthread_counted_neutral_pending.md`, `modeled_pthread_counted_pending_helper.md`, `modeled_pthread_counted_pending_wildcard.md`, `modeled_pthread_counted_overlap_rejected.md`, `modeled_pthread_thread_confined_resource_rejected.md`: worker transfer and join, failure to observe pending/stale counts, wildcard refusal, independent/reversed joins, and overlap/confinement rejection. The [worker authority protocol](worker-authority-protocol.md) maps each fixture to its replacement. |
| Shared abstract worker population | `modeled_pthread_counted_shared_join.md`, `modeled_pthread_counted_shared_forward_join.md`, `modeled_pthread_counted_shared_partial_then_create.md`, `modeled_pthread_counted_shared_retained.md`, `modeled_pthread_counted_shared_symbolic.md`, `modeled_pthread_counted_shared_neutral.md`, `modeled_pthread_counted_shared_observer.md`, `modeled_pthread_counted_shared_stale.md`, `modeled_pthread_counted_shared_early_count.md`, `modeled_pthread_counted_shared_missing_unit.md`: shared worker-ticket accounting, create failure, either join order, retained units, and early/stale/missing-unit refusals. These no-lock workers follow the frozen [worker authority protocol](worker-authority-protocol.md): only one worker may hold the authority, others borrow members, and join cannot retroactively authorize a worker update. |
| Count and protected memory with workers | `mutex_population_separate_body.md`, `mutex_population_missing_value_relation.md`: separation of contribution count from concrete counter value. Both count contributions that `pthread_create` workers consume, so they migrate with the shared worker population in milestone 6 chunk 3. The missing-value-relation case must continue to fail. |

`guarded_by` also appears in `src/languages/c/modeled_pthread_spec.md` and the implementation paths named below. The plain mutex tests without the annotation remain neighboring controls for ordinary mutex transfer; they are not authorization to drop the guarded negative cases.

For the explicitly named concurrent fixtures, the **fail** `expect` blocks are: `modeled_pthread_counted_before_join.md`, `modeled_pthread_counted_join_stale.md`, `modeled_pthread_counted_neutral_pending.md`, `modeled_pthread_counted_pending_helper.md`, `modeled_pthread_counted_pending_wildcard.md`, `modeled_pthread_counted_overlap_rejected.md`, `modeled_pthread_thread_confined_resource_rejected.md`, `modeled_pthread_counted_shared_early_count.md`, `modeled_pthread_counted_shared_missing_unit.md`, `modeled_pthread_counted_shared_observer.md`, `modeled_pthread_counted_shared_stale.md`, `population_conservation_local_mutex_bad_increment.md`, `population_mutex_cleanup_held.md`, `population_mutex_direct_read_unheld.md`, `population_mutex_helper_unheld.md`, `population_mutex_hidden_unit_at_release.md`, `population_mutex_incomplete_publication.md`, `population_mutex_second_custodian.md`, `mutex_population_body_missing.md`, `mutex_population_body_missing_direct.md`, `mutex_population_missing_value_relation.md`, `guarded_resource_unlock_unfolded_rejected.md`, `guarded_resource_wrong_mutex_rejected.md`, `modeled_pthread_mutex_early_destroy.md`, `modeled_pthread_mutex_parent_interference_rejects_stale.md`, `mutex_resource_quantity_requires_conservation.md`, and `mutex_unlock_missing_guard_and_invariant.md`. Every other individually named concurrent mdtest above has a success `expect` block. The `mutex_guard_*`, `mutex_use_*`, `mutex_helper_transfers*`, `mutex_lifetime_named*`, and `runtime_mutex_contract_*` families contain both passes and refusals; milestone 5 kept every checked-in outcome, as its migration record lists. The expected failures include unsuffixed `..._observer.md` and `..._cleanup_held.md`, so migration must not infer outcome from the filename.

When a group leaves legacy, record its fixtures or unchanged migrated source proof, positive claims, corresponding rejections, selected verification path, and verify/expand/audit evidence in the migration record below, then move its row to the migrated groups. The final switch must also inspect imported summaries, caches, and certificates; a successful new proof must never retry through legacy consumers.

## Migrated groups

### Source-backed examples and design groups

| Group and current path | Checked-in files | Existing property to preserve |
| --- | --- | --- |
| Sequential refcount project; authority | `examples/refcount/refcount.click`, `examples/refcount/README.md` | Counter equals the reference population through initialize, retain, symbolic retain/release, nonfinal release, final free, allocation failure, and callers. A final release needs the final member and reclaims once. All six related positive count-contract fixtures also use authority. |
| Shared parent; authority | `design/shared-heap-probes/shared_parent.click`, `design/shared-heap-probes/README.md`, `design/shared-heap-probes/click.project.json` | Parent wrappers carry child references through attachment, detach, nested calls, both destruction orders, surviving-parent reads, and final reclamation. The frozen main C verifies eight functions and audits 48 smart sites; the related boundary fixtures pass the full repository gate. |
| Bounded pool; authority | `examples/bounded-pool/bounded_pool.click`, `examples/bounded-pool/README.md`, `examples/bounded-pool/click.project.json` | `count(pool_object(pool, _))` is a per-pool wildcard total; exact objects and slot counts support checkout, return, resize, zero capacity, private object writes, and source-to-destination transfer. |
| Earlier authority design; non-executable | `design/concurrency-probes/shared-count-authority.md`, `design/concurrency-probes/explicit-authority.md`, `design/concurrency-probes/README.md` | Preserve the motivating hostile cases and protocol questions; these documents do not define the approved source interface. The migration issue supersedes the whole-population mutex-custody plan. |

`examples/jsonc-refcount/README.md` and the `mdtests/jsonc_refcount_{getter,increment,setter}.md` fixtures describe a separate JSON-C resource/model-field example; inspect them during the final source/doc audit, but their `count` search hits include ordinary C/API naming and should not be assumed to be Click population observations.

### Sequential mdtest dependency groups

All sequential fixtures in the following table select authority semantics. The paths in each row are relative to `mdtests/`. In addition to the listed fixtures, `authority_conditional_release_transfer.md`, `counted_resource_authority_retained_control.md`, and the three `authority_count_rejects_*.md` fixtures add checked authority regressions for the refcount row. The pass/fail ledger below comes from each fixture's checked-in `expect` block; names alone do not determine the expected result.

The loop/pure-expression row is a search-hit inventory, not a population
migration group: those fixtures use C functions named `count` or the standard
library's array-count function. None observes a declared-resource population.
Keep their existing proof coverage without introducing artificial authorities.

All 18 fixtures in the shared-parent lifecycle row select authority semantics.
Their contracts and intended refusals pass the full repository gate; see the
verification and audit evidence above.

| Group | Files and preserved behavior |
| --- | --- |
| Refcount and exact population basics | `counted_resource_refcount_transitions.md`, `counted_resource_population_body.md`, `counted_resource_population_lifetime.md`, `counted_resource_independent_populations.md`, `counted_release_preserves_nonfinal_allocation.md`, `population_initialized_cleanup.md`, `population_unit_needs_its_body.md`, `population_simple_exit_rejects_final_leak.md`: exact count/body relation, independent populations, nonfinal allocation preservation, initialization/finalization, and refusal to leak or produce a unit without its body. `counted_resource_rejects_minting.md`, `counted_resource_rejects_double_spend.md`, `counted_resource_transfer.md` pin ordinary ownership transfer and spend, even where they do not spell `count`. |
| Quantity, arithmetic, patterns, snapshots | `counted_distinct_populations_symbolic_entry.md`, `population_symbolic_increment_bounded.md`, `population_symbolic_increment_overflow.md`, `population_cleanup_rejects_partial_quantity.md`, `fold_rejects_a_negative_quantity.md`, `let_bound_constant_quantity.md`, `resource_pattern_counts_cross_contracts.md`, `resource_count_observe_witness.md`, `resource_count_predicate_snapshot.md`, `population_count_states_its_transition.md`, `population_count_across_a_produces_transition.md`, `c_contract_executes_resource_count.md`, `c_step_contract_resource_count_is_model_local.md`, `produced_population_count_in_ensured_predicate.md`, `consumed_population_count_in_ensured_predicate.md`, `predicate_without_count_ignores_resource_population.md`, `a_population_count_is_not_a_wrapped_total.md`: exact versus wildcard totals, bounded `int32` sums, nonnegative coefficients, contracts and predicates, historical snapshots, witnesses, and an unrelated predicate that must remain usable. |
| Open body, call, and return boundaries | `resource_population_open.md`, `population_open_calls_explicit_piece.md`, `call_inside_open_population_does_not_assume_its_body.md`, `population_call_with_restored_body.md`, `population_call_requires_closed_body.md`, `population_call_drops_the_cached_body_cell.md`, `population_call_keeps_what_it_may_and_drops_the_body_cell.md`, `population_call_rejects_open_alias.md`, `population_call_rejects_reentrant_restored_body.md`, `population_rejects_nested_open.md`, `population_rejects_nested_alias_open.md`, `load_origin_first_seen_per_function.md`, `return_population_rejects_missing_increment.md`, `return_population_rejects_missing_ownership.md`, `return_population_rejects_unupdated_sibling.md`, `return_population_rejects_wrong_release.md`: scoped restoration, no duplicated body access, call invalidation, and return checking. Some old positive body-open permissions must be replaced by ordinary ownership plus authority, while their memory and count claims remain. |
| Consumption at close and contribution | `counted_resource_contribution_counter.md`, `population_consumption_at_close.md`, `population_consumption_missing_contract.md`, `population_consumption_nested_overconsume.md`, `population_consumption_repeated.md`, `population_consumption_wrong_increment.md`: exact two, one spend across scope close/return, and refusal of missing, repeated, or incorrect consumption. |
| Shared parent lifecycle | `shared_heap_one_heap_parent.md`, `shared_heap_one_heap_parent_missing_child_ref.md`, `shared_heap_one_heap_parent_missing_retain.md`, `shared_heap_one_heap_parent_wrong_child.md`, `shared_heap_two_parent_branch_release.md`, `shared_heap_two_parent_branch_release_positive.md`, `shared_heap_two_parent_caller.md`, `shared_heap_population_lifecycles.md`, `shared_heap_population_certification.md`, `shared_heap_population_initialized_body_gap.md`, `shared_heap_composed_attach_detach.md`, `shared_heap_creator_release_repro.md`, `shared_heap_final_detach_repro.md`, `shared_heap_detach_old_resource_handoff.md`, `shared_heap_detach_leak_diagnostic.md`, `shared_heap_produced_ensure_transport.md`, `child_release_branch_on_count.md`, `parent_attach_call_frame.md`: parent-owned child membership, aliases, failed allocation, both destruction orders, preserved payload, and final free. Missing child/retain/wrong child and leak variants must still fail. |
| Loop and pure expression sites | `loop_old_count_invariant.md`, `loop_invariant_body.md`, `pure_click_functions.md`, `recursive_call_precondition_bounds_a_decremented_argument.md`, `recursive_call_precondition_refuses_a_decremented_lower_bound.md`, `recursion_measure_refusal_spells_its_measure_and_goal.md`: old versus current count in invariants and proof facts, predicate/pure-function evaluation, and diagnostics at recursive calls. |

List-valued named members now use checked algebraic schemas under authority. `authority_named_list_field_private_helper.md` preserves two distinct `List<int32>` models across a private-memory helper while authority is closed, then observes aggregate counts under exposed authority; companion negatives reject counts without exposed authority and a mismatched field type. Early protected-type expansion and later member lowering share one checked schema resolver. `resource_fields_reject_quantity.md` now selects authority semantics and rejects anonymous quantities for missing separately named fields, rather than claiming the family is uncountable. The original `resource_fields_reject_count.md` and `resource_fields_reject_hidden_count.md` now select authority and have converted to positive outcomes. The first retains `count(cell(p)) == 1` as an external precondition, adds explicit authority and named custody, and exercises a heap caller with sealed private memory, List model preservation, and cleanup. The second retains its forward-declared List-valued count function with explicit constructor type arguments. `authority_field_count_function_call.md` exercises the function before and after the same external call; fresh unfoldings use exposed authority. Companion negatives reject direct/hidden observations and external calls under a closed control, including a fresh unfolding after a prior authorized count. The reader contract is an external assumption, not verification of an absent C body. Imported named body opening and lifecycle effects are covered by the closing slice. Unary and wildcard preserving authority imports are supported, as described above. `resource_field_child_equations.md`, `resource_field_child_equation_rejects_other_start.md`, and `resource_unfold_binds_children_and_fields.md` protect distinct field identity and child binding independent of count.

### Checked-in `expect` outcomes

The following **fail** fixtures are the negative side of the sequential groups above. Every other explicitly named sequential mdtest in those groups has a success `expect` block at baseline. Preserve each failing claim's underlying obligation even if the diagnostic changes with the new permission model.

| Group | Expected-failure files |
| --- | --- |
| Arithmetic, quantity, patterns, and proof-expression boundaries | `a_population_count_is_not_a_wrapped_total.md`, `fold_rejects_a_negative_quantity.md`, `population_cleanup_rejects_partial_quantity.md`, `population_symbolic_increment_overflow.md`, `population_count_across_a_produces_transition.md`, `c_step_contract_resource_count_is_model_local.md`, `recursion_measure_refusal_spells_its_measure_and_goal.md`, `recursive_call_precondition_refuses_a_decremented_lower_bound.md`. |
| Body and call boundaries | `call_inside_open_population_does_not_assume_its_body.md`, `population_call_drops_the_cached_body_cell.md`, `population_call_rejects_open_alias.md`, `population_call_rejects_reentrant_restored_body.md`, `population_call_requires_closed_body.md`, `population_rejects_nested_alias_open.md`, `population_rejects_nested_open.md`, `population_unit_needs_its_body.md`. |
| Population updates and return | `counted_resource_rejects_double_spend.md`, `counted_resource_rejects_minting.md`, `population_simple_exit_rejects_final_leak.md`, `population_consumption_missing_contract.md`, `population_consumption_nested_overconsume.md`, `population_consumption_repeated.md`, `population_consumption_wrong_increment.md`, `return_population_rejects_missing_increment.md`, `return_population_rejects_missing_ownership.md`, `return_population_rejects_unupdated_sibling.md`, `return_population_rejects_wrong_release.md`. |
| Parent identity and lifetime | `shared_heap_one_heap_parent_missing_child_ref.md`, `shared_heap_one_heap_parent_missing_retain.md`, `shared_heap_one_heap_parent_wrong_child.md`, `shared_heap_two_parent_branch_release.md`, `shared_heap_population_initialized_body_gap.md`, `shared_heap_detach_leak_diagnostic.md`, `resource_field_child_equation_rejects_other_start.md`. The unsuffixed two-parent branch fixture is a negative control; its `..._positive.md` counterpart is the passing claim. |
| Field classification | `resource_fields_reject_quantity.md` rejects anonymous quantities requiring separately named members. `authority_field_count_direct_missing_authority.md`, `authority_field_count_function_missing_authority.md`, and `authority_field_count_external_missing_authority.md` reject observations or calls without exposed authority. The former direct/hidden count refusals have converted to positives with these permission controls. |

## Discovery commands

The following commands, run from the repository root, find the checked-in consumers when this inventory is updated. Review matches in context: C functions named `count`, prose mentioning quantities, and Rust variables named `count` are not population observations. The mdtest list is intentionally grouped below by proof dependency rather than by every syntactic occurrence.

```sh
rg -l '\bcount\s*\(' examples mdtests design docs src tests
rg -l '\bguarded_by\b' examples mdtests design docs src tests
rg -l '\b(owns|views|consumes|produces)\s+[^;\n]*\s+of\s+\w+\s*\(' examples mdtests design docs src tests
rg -l 'field.*count|count.*field|is_countable|CountedPopulation' examples mdtests design docs src tests
```

The third query finds explicit coefficient clauses, including unrelated resource quantities. Repeated `owns`/`consumes` clauses also encode quantities and require contextual review. The `count` search covers body facts, contracts, predicates, snapshots, and loop invariants; those are distinct authority-dependency sites, not one interchangeable test.

## Kernel, surface, and documentation consumers

The kernel regression anchors are `src/kernel/tests/resource_tests.rs` (including `resource_field_schemas_are_typed_shared_and_non_countable`, population/count witness tests), `src/kernel/tests/contract_execution_tests.rs` (cross-contract population counts), and `src/kernel/tests/resource_scaling_tests.rs` (partition cost and alias refusal). Count-related tests also occur in `src/kernel/tests/{canonicalization,execution,iterated_ownership,loan_model,memory_reasoning,state_identity}_tests.rs` and `src/kernel/functions/callback_contract_tests.rs`; use the discovery commands before changing the kernel. The executable mechanism currently spans `src/kernel/primitives/counted_populations.rs`, `src/kernel/population_access.rs`, `src/kernel/proof/{population_initialization,population_consumption}.rs`, `src/kernel/resource_tracker/`, `src/kernel/mutexes/{population,invariant_interface,assumed_protocol}.rs`, and `src/kernel/primitives/contracts.rs`. Surface classification and lowering occur in `src/surface.rs`, `src/surface/parser.rs`, `src/surface/validation/{definition_validation,declaration_expansion}.rs`, and `src/surface/verification.rs`. These are code locations, not approved new semantics.

The existing `constructs`/`construct(...)` route is a separate establishment surface to review: parsing is in `src/surface/parser.rs`, declaration checks in `src/surface/validation/definition_validation.rs`, outcome application in `src/surface/proof/proof_object/step_application.rs`, and the checked operation in `src/kernel/functions.rs` through `src/kernel/api.rs`. It currently authorizes exactly one owned abstract token from a function contract, with duplicate-token rejection; it does not establish a population authority today.

Public explanations to revise as groups migrate are `docs/concepts/resources.md` (quantity, shared body, count, wildcard, worker reservation, `guarded_by`), `docs/reference/language/index.md` (resource syntax and semantics), `docs/reference/language/grammar.md`, `docs/reference/glossary.md`, `docs/reference/examples.md`, and `examples/README.md`. Source-backed internal explanations include `docs/internals/resource-invariants.md`, `docs/internals/resource-parameters.md`, `docs/internals/mutex-resource-contracts.md`, `docs/internals/concurrency-contracts-and-diagnostics.md`, `docs/internals/resource-tracker.md`, `docs/internals/kernel.md`, and `docs/internals/separation-logic.md`. `docs/concepts/loops-and-invariants.md`, `docs/concepts/pure-functions.md`, and `docs/concepts/predicates.md` cover count-bearing proof-expression contexts. Search other docs with the commands above at the final default switch; a documentation example can be a consumer even when no standalone mdtest file has the same name.

## Migration record

Evidence below was recorded as each group landed. Later entries supersede limitations stated in earlier ones; the migration issue's scope boundary lists the shapes that remain unsupported.

### Foundations (earlier checkpoints 0–5)

Kernel and source support now check authority custody, current versus historical
counts, real birth/consumption, private-body access, and independently checked
ordinary helper contracts. Helper populations enter with arbitrary totals and
no creator rights. Sequential refcount, symbolic batches, and shared-parent
ownership have migrated. Field-free wildcard populations support concrete-member
creation, consumption, cross-pool moves, private memory and invariants, contained
ordinary resources, and exact member observations. A control can package two
same-anchor authorities with counter facts; direct and nested checkout preserve
that control and caller-retained slots. No new parameter syntax is needed.

The original bounded-pool sidecar, named-member identity and checked lifecycle
helpers, and all remaining sequential groups are complete. Mutex/worker migration
and the default switch remain unfinished.

#### Sequential refcount

`examples/refcount/refcount.click` now selects authority semantics for its
unchanged C files. It verifies all seven functions: initialization, one and
symbolic-batch retain/release, final release with allocation reclamation, and
the complete pipeline including allocation failure. Four positive count-contract
fixtures now use authority: population/body equality, population lifetime,
independent populations, and retain/nonfinal release. Their external entry
counts are arbitrary and observed through checked current control ownership.
The missing-private-body negative and ordinary abstract transfer fixture also
use authority. The nonfinal-allocation and initialized-cleanup fixtures now
also use authority, preserving their C and all original count postconditions.
Checked empty authority cleanup preserves a read-only zero for the exact
family, including after free. Initialization uses an ordinary storage resource
containing authority, independent of the not-yet-initialized C counter. The
sequential refcount group is complete.

#### Shared-parent ownership

The frozen `design/shared-heap-probes/shared_parent.c` now has an authority
sidecar, selected by `design/shared-heap-probes/click.project.json`. Its eight
function proofs verify, and all 48 smart sites pass expansion audit. The main
proof covers initialization, both destruction orders, allocation failure,
surviving-parent payload reads, and complete reclamation.

All 18 shared-parent mdtests listed in the lifecycle row below now select
`resource_semantics=authority` in their Click fence. This includes
`shared_heap_produced_ensure_transport.md`, which exercises ordinary named
resource field transport under the authority profile without introducing a
population. The other fixtures use empty reference members and separately
owned control containing memory, allocation, and exact population authority;
uninitialized storage omits the counter invariant until initialization.
Named parent resources use ordinary checked memory exchange, preserving the
population ledger. No proof retries through the legacy population path.

The migrated detach contracts return an already borrowed surviving reference
through `owns`; they no longer promise an additional duplicate output. The
entry-pointer handoff returns control conditionally using the original
pointer. External callers state genuine signed-counter overflow bounds for
one or two increments, rather than inferring the total from locally held
members. Fixtures that require a creator total of one state that assumption
explicitly. C source and payload/lifetime guarantees remain unchanged.

The straight two-parent fixture has a nonterminal decrement-only release: its
existing `Count > 1` precondition preserves control, and detach borrows one
surviving member while consuming one other member. This admits the same two
input units and returns one with preserved identity; unconditional control
return is stronger than its earlier guarded return. The weaker candidate that
consumed two units and produced one, with control guarded by
`old(count(child_ref(p->kid))) > 1`, was unsupported at migration time. A later
recheck found that the guarded control return now verifies, and that the
callee proves the two-to-one shape, but callers still cannot apply it. That
remaining refusal is filed as
`bugs/a-verified-two-to-one-quantity-contract-cannot-be-applied.md`.
The main and branch fixtures retain conditional control return and final-free
coverage. All C and payload claims remain unchanged.

Focused verification and expansion audits pass for the main proof and the
related positive boundary fixtures. The main proof audits 48 smart sites;
one-parent, two-parent branch, attach-frame, branch-release, and straight
two-parent fixtures audit another 69. Composed attach/detach, creator release,
population certification, final detach, and entry-pointer handoff also verify
and audit. Missing-member, missing-retain, wrong-child, false final-count,
initialized-body-gap, and detach-leak negatives retain their intended refusals.
Checkpoint 5 is complete: the full `scripts/check.sh --no-fail-fast` gate passes,
including all 2,569 mdtests and the frozen shared-heap example checks.

### Milestone 1: bounded pool

The original bounded-pool project now uses authority semantics, with the former
companion consolidated into `examples/bounded-pool/bounded_pool.click`. All
original C is unchanged. Its 16 claims cover all eleven original C functions
and five arithmetic lemmas. The full `scripts/check.sh` gate passed: 4,720 unit/integration tests and 190
fixture tests. The complete expansion audit passed all 99 smart sites across
all 16 claims. Milestone 1 is complete.

- Initialization explicitly receives storage and both empty authorities; it
  cannot mint authority for an external pointer. Cleanup consumes the complete
  entry-capacity slot batch, proves both populations empty, retires both
  authorities, and returns ordinary memory. Zero quantities use the same rules.
- Checkout and return exchange a concrete member's private memory and one slot
  under the control's authority. Helpers preserve neighbors, exact identity,
  values, conservation, and arithmetic bounds. Private writes need only the
  owned member; the pool control stays closed.
- Symbolic growth/shrink preserve existing populations, handle zero, and check
  signed arithmetic. A helper returns its exact freshly born symbolic batch;
  caller ownership remains distinct from global population counts.
- Transfer checks all four unit effects under the two controls and restores
  both invariants. The original transfer pipeline composes initialization,
  checkout, and transfer, preserving the object's value and returning both
  controls plus the destination member and source slot.

The reduced capability checkpoints remain covered by
`authority_pool_control_return_full.md`, `authority_pool_control_init_nested.md`,
`authority_pool_control_cleanup_helper.md`, `authority_pool_cleanup_field_quantity.md`,
`authority_symbolic_batch_helper.md`, `authority_symbolic_batch_cleanup_helper.md`,
`authority_pool_grow_helper.md`, `authority_four_effect_exchange.md`,
`authority_two_control_init_call.md`, and `authority_two_control_birth_helpers.md`,
with their negative companions and independent kernel/scaling checks. These
cover missing authority/custody, wrong identities or quantities, duplicate
transfer, missing consumption, extra birth, overflow, and nonempty retirement.
The two-control call boundary projects callee returns and untouched caller
controls under their respective ledgers. Ordinary resource openings establish
memory framing; no C workaround or new syntax is used.

A stack-object transfer bridge was unnecessary for these external-pointer C
pipelines and remains outside the milestone. Additional symbolic subset or
batch-splitting machinery stays driven by real consumers. The speculative
cache repair remains removed.

#### Capability fixtures

The `authority_wildcard_*` fixture group adds concrete, field-free
`R(anchor, _, ...)` population scopes and aggregate count observations.
The `authority_wildcard_helper_*` fixtures add ordinary borrow-and-return
contracts for one concrete member and wildcard authority, including nested
calls. Helper entry imports an arbitrary total; it cannot establish authority
or equate that total to its locally owned member quantity.
The `authority_wildcard_create_helper*` fixtures additionally create one
field-free member from an authority-only helper input. They preserve arbitrary
entry totals, require checked count bounds, retain concrete output arguments,
and exercise both direct and nested creation while the caller holds other
members. The `authority_wildcard_consume_helper*` fixtures consume one exact
entry member while returning authority, including nested calls. The caller
retains other members, observes the checked decrement, and cannot reuse the
consumed member. Return certification rejects a declared consumption without
an actual transition. Kernel regressions cover identity, authority and member
custody, repeated transitions, and scaling beside unrelated imports.
The `authority_wildcard_private_body*` fixtures cover disjoint private memory
bodies, nested opening and closing without membership changes, and a member-only
helper while the caller retains authority and another member. They reject
missing member or memory ownership, overlapping bodies, and count observations
without authority.
The `authority_wildcard_consume_private_body*` fixtures combine consumption
with private memory: direct and nested helpers return the selected member's
owned range through `produces`, preserve caller-retained members, and decrease
the arbitrary population total by one. They reject missing authority,
wrong-member selection, a missing consumption, and reuse after consumption or
memory reclamation.
The `authority_wildcard_create_private_body*` fixtures cover the inverse:
direct and nested helpers consume an owned range and produce a new member
whose body owns that range. The caller retains another member and observes
the incremented total. Regressions reject missing memory or authority,
duplicate membership or independent body ownership, and a missing overflow
bound. Existing checked exchanges support this without verifier changes.
The `authority_wildcard_transfer_private_body*` fixtures move one unit member
between two wildcard authorities through direct and nested helpers, retaining
private memory and caller-owned members in both pools. Both entry totals are
arbitrary; each ledger checks the exact decrement or increment. Rejections
cover absent authority or bounds, missing exchange, incorrect totals, aliased
pools, and reuse of the consumed source membership. An unrelated member may
be framed beside an authority; it is not imported into that authority's pool.
The `authority_wildcard_body_facts*` fixtures add private invariants to unit
memory-bearing members. Folding checks current facts, opening/closing maintains
them without authority, and consumption exposes the exact member's invariant.
Two disjoint members retain their totals and private values. Rejections cover
false birth, invalidating writes at close, and an invariant reading a cell
outside its own body even when the caller owns that cell. Kernel regressions
reject unchecked birth and forged facts during consumption or checked event application.
The `authority_wildcard_contained_resource*` fixtures add ordinary owned
resources inside a member body. Creation helpers consume the exact child;
consumption helpers return it; member-only helpers open both layers. Direct
and nested callers retain another member and preserve the child family's
population total. Rejections cover missing or wrong children, independent
return of a child retained in a member, wrong returned identity, and an
unchanged total promised for a birth. `authority_wildcard_contained_object`
covers the built-in `owns object(p)` form. The kernel checks the exact body
exchange, and helper custody follows only the explicit contained-resource
frontier, without scanning the caller frame.
This discovery group preceded the bounded-pool migration recorded above;
the original sidecar now selects authority semantics.

The `authority_wildcard_exact_count*` fixtures distinguish exact member counts
from wildcard totals, including creation and consumption helper contracts,
retained neighboring members, equal-member multiplicity, and refusal to infer
a global exact count from local custody. Kernel regressions cover authority
transfer, unresolved indices, arbitrary entry counts, and indexed scaling.

The `authority_family_exchange*` fixtures add one unit consumption and one
unit production from different families at the same anchor, with explicit
borrowed unary/wildcard authorities and ordinary object ownership. Direct and
nested caller proofs preserve retained members and check both count changes.
Rejections cover missing authority or object ownership, missing consumption or
production, and equating a unary total to local custody. Kernel checks cover
admission and checked external body extents. The unchanged stack-object case
is preserved as a separate expected rejection: implicit local access is not
currently transferable object ownership.

The `authority_pool_control*` fixtures package both population authorities and
C pool fields in one ordinary control. Direct and nested checkout helpers
restore the checked-out count and capacity equations. A caller retains another
slot while passing the control and consuming one slot. Negative fixtures
reject missing effects/authority, duplicate authority, and a wrong C increment.
Kernel regressions check both imported custodies, arbitrary totals without
creation rights, and the three required domains for balanced unit arithmetic.
Indexed domain-query scaling is checked beside unrelated facts. Support is
limited to one/two authorities at the same anchor with a field-free control;
the bounded-pool sidecar and general wrapper/batch support remain separate.

`authority_pool_control_return_full.md` adds direct and nested return, with an
exact concrete input member imported alongside its folded control. Both count
invariants and the ordinary `valid_pool(pool)` predicate are restored, private
memory is returned, and a caller retains a neighboring slot. Its signed-sum proof uses ordinary arithmetic lemmas rather
than new syntax; reversed summands retain all domain checks. Kernel imports
reject missing ownership, multiple selected inputs, and wrong pool identity.
`authority_pool_control_init_nested.md` packages explicitly passed empty
populations through standalone arbitrary-capacity initialization and a nested
capacity-two call. Both prove the ordinary `valid_pool` predicate after
replacing storage with control; the caller also observes the current slot count.
The checked rewrite and helper return authenticate only their explicit control
frontier and preserve existing population identity, totals, and custody. An
unowned wrapper or a wrapper without authenticated authority cannot supply
count permission. Numerical unary batches compose with unit updates without
per-unit iteration; tests reject overflow, insufficient custody, and use after
lending authority. Zero quantities do not grant member rights.

`authority_pool_control_two_members.md` initializes an external pool, checks out
both private objects, writes 11/22 with control closed, and returns them in the
opposite order. Its final slot quantity is two. Exact member custody and call
memoization are indexed by identity; borrowing one member does not borrow its
neighbor. For a deterministic positive exclusive memory footprint, equal
arguments cannot describe two live instances, so its owned exact count is one.
A remembered exact absence is invalidated by a subsequent unresolved birth;
an empty whole population entails every exact count is zero. Empty-body
families keep their existing conservative rule. Kernel tests cover wrong
members, double spend, absence invalidation and multi-size custody scaling.
An aliased second birth is rejected by a source regression. Constant ownership
quantities are now observed from an indexed tally without merging or duplicating
retained occurrences; views contribute no units and arithmetic never wraps.

### Milestone 2: member identity and proof fields

1. **Occurrence identity:** The existing resource context retains each named
   instance's identity and proof fields. Population bookkeeping counts births
   and consumption independently of field values, with checked certificate
   successors. Equal arguments do not merge member states.
2. **Local lifecycle and counts:** Existing `authority(...)`, `count(...)`,
   `fold`, and `unfold` support local field-bearing exact and wildcard families.
   Both aggregate and exact counts include independently owned occurrences.
   Local creation and consumption require the governing authority.
3. **Preserving helper transport:** Ordinary named `owns` inputs and explicit
   field postconditions retain members across calls. A helper can unfold,
   update, and restore private memory while the caller keeps its authority
   control closed and retains another member. The same occurrence remains
   reserved across the preserving call; this does not authorize counting.
4. **Replacement negatives:** Checks reject overlapping private memory,
   duplicate helper inputs, count observations without authority, unauthorized
   lifecycle changes, late establishment, and retirement with live members.
   Anonymous quantities cannot manufacture missing instance fields. Legacy
   field-count rejection fixtures were retained until their Milestone 3 migration.

**Exit gate passed:** Two disjoint field-bearing members preserve identity and
private state; exclusive-memory conflicts and unauthorized transitions fail.
Field presence does not select authority-mode family countability. No new
surface syntax or changes to existing C were needed. The full `scripts/check.sh`
gate passed 4,723 unit/integration tests and 190 fixture tests; all 48 new
named-member expansion-audit sites passed.

**Milestone 2 boundary:** Named-member helper lifecycle effects were deferred
here and are completed by Milestone 3 below. Calls cannot silently remove or
add a tracked member without updating the ledger. Symbolic quantities of heterogeneous
instances and general sums over fields are not implemented. List-valued field
descriptions are supported by the Milestone 3 slice. Local lifecycle operations and preserving helpers are supported.
These limits do not restrict ordinary uncounted named resources.

The `authority_named_field_*` fixtures add local field-bearing families with
exact and wildcard authority. Occurrences with equal arguments retain distinct
identities and proof fields; aggregate/exact counts track local birth and
consumption. Disjoint private bodies can be updated through preserving ordinary
helper contracts while the caller's authority control remains closed.
Negatives cover overlapping memory, duplicate helper inputs, missing authority
for counts or lifecycle changes, late establishment, and premature retirement.
Named-member helper creation/consumption with explicit authority is completed
by the Milestone 3 closing slice. Heterogeneous symbolic instance batches and
general sums over fields remain outside the implemented boundary. List-valued field descriptions are covered by the
Milestone 3 slice below. Milestone 2 is complete
for this boundary: the full gate passed 4,723 unit/integration tests and 190
fixture tests; all 48 new named-member expansion-audit sites passed.

### Milestone 3: remaining sequential accounting

**Closing slice:** Named births and deaths now cross direct and nested verified
helpers under their explicit governing authority. Checked resource partitions
retain exact identity, fields, private storage, and framed occurrences. Unary
and wildcard imports keep arbitrary entry totals; births require increment
bounds, and only consumed entry occurrences establish entry-count lower bounds.
A birth followed by consumption does not invent an entry member. Indexed exact
counts retain concrete selections and refuse unresolved neighboring effects.
Repeated birth/death, absent authority or birth, false totals, and spent-instance
reuse remain rejected. Authority-mode returns use the authority ledger without
legacy population-transition fallback. Multi-size kernel checks cover unrelated
imports and growing related death receipts.

The two scalar logical callback controls now use authority mode and explicit
ordinary resource models, preserving their scalar signatures, exact-one logical
claim, and model-local false-result refusal. This follows the resolved decision
to retire integer-only global populations. Pointer-anchored Count preservation
remains covered by the existing named callback fixtures and the Count-specific
refinement/model-local companions. Targeted execution-theorem expansion retains
the project mode, so its independently checked certificate agrees with ordinary
verification. Ordinary named models
can cross preserving assumed interfaces without an artificial population anchor;
assumed interfaces still cannot perform named population lifecycle effects.

**Recovery closure:** The owned-count and predicate recoveries are superseded by
landed, checked replacements. The pool-member recovery's private-memory consumption frontier now verifies
as a repository fixture with its original C preserved. Its never-green implicit
stack-body transfer proposal is retained as an unchanged-C refusal at the
existing local-storage ownership boundary; a separate explicit-storage helper
checks cross-pool model transfer and a caller-framed occurrence. Earlier local/private/member refusal probes have
named-field replacements. No Milestone 3 implementation or regression depends on
an uncommitted recovery worktree. The unrelated C++/snapshot experiments remain
preserved in the original recovery archive; they are not migration dependencies.

**Exit gate:** All sequential population-consumer groups have authority-mode
replacements, including their diagnostic and negative controls. The loop/pure
expression search hits and ordinary child-model equations do not observe resource
populations. The retained negative-quantity legacy fixture is an explicit
Milestone 6 control with a checked authority replacement. Mutex and worker groups
remain listed for Milestones 4 and 5. Symbolic heterogeneous named batches,
general sums over fields, and assumed named lifecycle interfaces remain outside
this milestone's supported boundary.

**Completion validation:** The full `scripts/check.sh --no-fail-fast` gate
passed 5,074 unit/integration tests and 368 fixture tests, with 23 configured
skips. All 54 closing smart sites passed expansion, retained/cold certificate
rechecking, and fixed-point audits. The callback Count refinement has a
source-backed regression for authority-mode targeted expansion. Existing C
and C++ fences remain byte-for-byte unchanged.

**Preserving named authority imports:** Unary and wildcard field-bearing
authorities import an arbitrary total without anonymous member rights. Named identity and fields
remain in the checked resource context; ordinary preserving calls return both
that custody and authority. Count recovers the declared field schema through
an immutable indexed import map. Regressions retain two distinct members with
equal arguments, and forward-declared List functions preserve Count observations
across calls. Negatives reject missing authority, exact totals invented from
local ownership, and unauthorized imported named lifecycle operations. Kernel checks enforce
preserving imports and bounded lookup work beside growing unrelated populations.
Wildcard helpers preserve aggregate and exact observations while other named
members stay framed; an authority-only helper preserves them with all members
framed. Regressions reject invented aggregate/exact totals and unauthorized lifecycle changes.
External and named callback contracts now build entry contexts in the selected
resource semantics. Assumed interfaces may preserve explicitly owned authority
and named occurrences through the shared checked call engine. They cannot birth
or spend named members, replace identity, or introduce anonymous lifecycle
rights. Regressions retain unary/wildcard counts and List-valued fields, and
reject missing authority, duplicate binders, another anchor, and consumption.
Named lifecycle transfers at these assumed interfaces remain unsupported. The two original field-count
controls now select authority and pass: the external interface retains its
original count precondition with named custody, and the forward-declared pure
function keeps its List-valued count body. A caller exercises sealed private
memory, model preservation, and cleanup. Companion negatives reject direct or
hidden observations and calls when authority is closed, including after a prior
authorized observation. The external reader remains an explicit assumption;
this does not certify its absent C body.

**Unary named consumption at standalone entries:** Checked unfolds record exact
member identities and relative deaths without assuming that locally owned
members exhaust the imported population. Input-clause receipts do not restore
live custody. Source regressions cover unfolds before and after C execution,
checked body facts, and a framed named member. False totals, closed authority,
missing deaths, and partially checked consumption are rejected. Return-rewrite
certificates check the requested direction and independently recheck body facts
and the ledger; repeated folds remain rejected. Kernel regressions cover
identity, duplicate death, equal-field distinct occurrences, no anonymous
custody, and logarithmic indexed work beside 16/64/256 unrelated imports.
This standalone slice left named creation, wildcard lifecycle operations, and
caller-side consumption guarded. The closing slice below replaces those guards
with checked effects.

**List-valued named fields:** Protected resource types and named member lowering
now share checked algebraic field schemas. A private-memory preserving helper
proof retains two distinct List values while authority is closed, and observes
counts after reopening it. Negatives reject anonymous field-bearing quantities,
missing count authority, and incorrect model types. The original field-count controls now use authority with preserving external
interfaces; imported body opening and lifecycle effects use the closing slice below. Unary and wildcard preserving authority imports are supported
by the slice above. This slice does not add named helper
lifecycle effects or sums over model fields.

**Count-only observation slice:** `resource_count_observe_witness.md` now uses
explicit authority with both original C functions and lower-bound claims
unchanged. Observation checks the exact owned quantity against the immutable
authority ledger; it does not project private bodies or change memory, member
custody, or population state. Unary helper entry retains numeric and symbolic
batch custody independently of the arbitrary global total. Regressions cover
zero quantity, missing authority, closed private memory, and refusal to equate
local symbolic custody with the global total. Kernel checks reject forged facts
and resource deltas, with deterministic work checks beside unrelated state.

**Load-origin fixture slice:** The first-seen-per-function regression uses
explicit empty slot authorities and checked capacity-batch creation. Pool
memory remains independently owned; the reset helper performs no population
operation. The unchanged zero-reset and two-pool C pipelines preserve their
postconditions and the first pool's predicate across the second call.

**Abstract-token member slice:** `resource_pattern_counts_cross_contracts.md`
uses explicit wildcard authority with the original checkout, return, and
roundtrip C programs unchanged. A member privately owns its exact abstract
`available(object)` token; creation consumes the token and consumption returns
it. Return accepts arbitrary entry totals, with its decrement bound supplied by
checked member custody rather than an exact-count-equals-one requirement.
Contract entry retains the checked wildcard bound as well as the exact bound.
A helper-created nonexclusive member can subsequently be consumed by its exact
current owner; identity and single-spend checks remain enforced. The three
proofs and nine expansion-audit sites pass.

**First small slice:** The constant-quantity fixtures now use authority semantics.
`let_bound_constant_quantity.md` packages allocation, counter memory, and
authority in an ordinary control; its contract still consumes the quantity
selected by `let k = 2`. `fold_rejects_a_negative_quantity.md` preserves the
zero/negative boundary with a separate reference family and owned counter
memory. Negative coefficients report the required nonnegative fact rather
than `InvalidQuantity`. C source is unchanged.

**Mixed-birth slice:** The original
`population_symbolic_increment_{bounded,overflow}.md` pair now uses explicit
authority and defined-addition contracts with unchanged C. A checked symbolic
birth can be followed by numerical births and consumption of those separately
held numerical fragments; the count retains both deltas. The bounded case
preserves `count == n + 1`; the overflowing case rejects the second helper's
undefined addition. Numerical custody transfers independently of the symbolic
batch, preserving exact quantities, authority custody, and single-spend checks.
An arbitrary-entry companion and a false-total companion check that neither
the entry total nor the unit delta disappears. Signed regrouping checks all
three addition domains rather than accepting modular equality as a domain proof.
This does not admit splitting a symbolic batch or mixing a symbolic input/spend
with numerical effects; those remain separate ledger boundaries.

**Overflow-total control:** `a_population_count_is_not_a_wrapped_total.md`
now uses explicit authority and a defined-addition contract, with all three
original C functions and their count claims retained. The first two-billion
symbolic birth succeeds; the checked transition rejects the second birth
before publishing a wrapped count. The original numeric caller verifies
independently with its exact `3 + 4 == 7` total. Companion fixtures admit a
single large symbolic birth and a numeric total exactly at `2147483647`, and
reject a further numerical birth. All twelve positive expansion sites audit.
This initial slice migrated the overflow refusal without adding general
repeated symbolic births; the later composable-birth slice supplies that
broader ledger capability.

**Exactly known batch slice:** A symbolic quantity pinned by a recorded exact
integer equality now uses the numeric birth ledger. The original repeated-birth
C verifies with `k == 1000000000` and an exact total of two billion, while the
original two-billion overflow caller remains rejected at its second call.
Exact quantities also select numerical fragments for ordinary helper transfer
and consumption, leaving the other batch framed. Missing authority, invented
totals, and overconsumption remain rejected. Bounds alone do not normalize a
quantity, and genuinely symbolic entry custody keeps its representation on
spend. The lookup uses the existing indexed exact-equality map; kernel scaling
coverage checks 16/64/256 unrelated facts and populations. A numeric birth beyond the signed count limit now reports
`PopulationCountOverflow`, rather than missing member custody; the existing
symbolic-increment overflow control retains its C and second-call refusal.
This does not add
general repeated symbolic births or symbolic batch splitting.

**Global-count decision resolved:** Remove the two obsolete fixtures that
counted across all independently anchored populations or used integer-only
population identities. No arena abstraction or new syntax is required for this
migration. Existing fixed-anchor wildcard fixtures retain scoped aggregation
coverage. The independent symbolic-entry fixture now owns each exact family's
authority; it still needs no invented bound on the sum of unrelated counts.

**Predicate-snapshot slice:** `resource_count_predicate_snapshot.md` now uses
authority semantics. An ordinary control owns the counter and reference-family
authority; references remain separate members. The unchanged retain operation
increments the counter, creates one member, establishes the new predicate,
and restores the control. The proof retains the current predicate and returned
pointer claims without reusing the entry predicate for the updated state.

**Exact-two slice:** `counted_resource_contribution_counter.md` now uses
authority semantics for all seven original C functions. Empty contribution
members are separate from an ordinary counter/authority control. Initialization
takes storage with empty authority; each increment explicitly consumes one
member and states its count and memory effects. Both caller pipelines prove two
contributions, and final cleanup consumes the remaining member before retiring
authority and returning memory. Whole symbolic cleanup and the zero/one-value
cleanup cases retain their original results. C source is unchanged.

**Early-consumption slice:** `population_consumption_at_close.md` now uses
explicit member consumption inside an ordinary control scope. Reopening does
not spend again; nested calls and both reporting branches retain the one
checked effect. The caller proves two contributions and fully retires authority.
The wrong-increment negative uses the same protocol and fails on the concrete
counter/count invariant. All five proofs and ten audit sites pass.

**Local concrete-batch slice:** Locally established numerical batches now share
the unit custody ledger, so a batch of three can be consumed as one and two.
Zero changes still require authority. The focused fixture and kernel tests
cover splitting, overconsumption, overflow, live-member retirement, and exact
wildcard member counts. Deterministic quantity scaling checks constant work;
true symbolic-batch/unit mixing remains a separate boundary.

**Contract-transition slice:** The count-transition positive and negative now
use explicit authority and a checked member birth. The positive states the
entry-to-post count relation; the negative rejects its fixed post-count claim.
The produced-population predicate fixture and its ordinary caller also select
authority semantics. They require an empty entry family explicitly and retain
the original C and ensured predicate through positive and zero quantities.

**Owned-count certification slice:** Independent contract certification now
retains the count evaluator's authenticated member bounds under authority
semantics. A helper with one owned member and matching authority can certify
`1 <= count(...)` without assuming the global total is exactly one. Consumption
uses the updated count, and neither an untracked resource fact nor a member
without authority supplies the bound. The `authority_owned_count_*` regressions
cover helper calls, nonnegative remaining counts, and exact/stale/unauthorized
count refusals. This does not enable general `observe` in authority mode.

**Private predicate facts slice:** Private member fact instantiation retains
the current verification model and population state instead of starting a
legacy state. Definition-local parameters and the member's own body remain
the only local bindings and read permissions. The count-independent memory
predicate fixture now uses explicit empty-family authority and keeps its
original C and predicate claim through a checked birth. Foreign-memory facts
remain rejected, and checking work stays bounded beside unrelated caller locals.

**Consumed-predicate slice:** `consumed_population_count_in_ensured_predicate.md`
now uses an ordinary accounting control containing C fields and both family
authorities. Explicit symbolic member consumption and the unchanged C update
restore the current predicate and the private count equation. A companion
rejects a declared consumption that the proof omits; a C update alone cannot
restore that equation. The original C and ensured claim are preserved.

**Predicate precondition repair:** Count-bearing predicates capture the
authority ledger rather than a legacy empty model. Nested predicates retain
the same count-only read witness; it neither supplies execution resources nor
permits authority, anonymous-member, or named-member lifecycle changes.
Definition dependencies select the resource snapshot while count-independent
predicates retain their identity. Positive and false-zero regressions check
the unchanged C counter, and kernel tests check captured counts, forbidden
transfers, dependency registration, and deterministic scanning work.
An explicit subtraction lemma restores the existing consumption predicate
under the correct model and returns its sum's definedness for invariant close.

**Single-spend negative slice:** The missing-contract, repeated-consumption,
and nested-overconsumption fixtures now separate member custody from an
ordinary counter/authority control. Each retains its unchanged C and reaches
the intended missing-member return obligation after explicit checked spends.
Restoring the count equation cannot authorize an undeclared second consumption
or return a member already spent by the proof or a helper.

**Partial-cleanup slice:** `population_cleanup_rejects_partial_quantity.md`
now rejects a partial spend that would restore a control with the wrong
count/counter relation. A whole-quantity companion with the same C consumes
all members after exposing the control and returns its memory and authority.
This preserves the cleanup refusal without reintroducing the legacy blanket
requirement that every quantity consumption be a whole-population operation.

**Scoped-body slice:** The population-opening positive, explicit-piece helper,
and restored-body helper fixtures now use ordinary counter/authority controls
with unchanged C. Their reentrant, aliased, and nested-opening companions
reject duplicating a suspended control. An unrelated call cannot assume the
caller-open control invariant after a contradictory store. Opening does not
create or consume members; body facts must be restored before closing.

**Cached-call slice:** The paired cached-body fixtures now borrow an ordinary
counter/authority control and explicitly create the retained member before
return. The unchanged caller preserves its cached pre-call value and proves
it equals the post-call count minus one, while the arbitrary-result negative
still fails. An unrelated call preserves the caller-framed saved cell without
assuming a temporarily broken control invariant.

**Return-refusal slice:** All four return-population negatives now select
authority semantics. Explicit births/consumption cannot restore a missing
increment, an untouched sibling counter, or a nonfinal counter cleared to zero.
The missing-write case owns count authority but only views C memory, and fails
on the store itself. Every original C program and refusal obligation is retained.

#### Fixture notes

**Milestone 3 exit:** Every sequential population-consumer row below now has an
authority-mode replacement. `c_contract_executes_resource_count.md` preserves
its exact-one logical model through a checked callback refinement;
`c_step_contract_resource_count_is_model_local.md` retains the unchanged scalar
C and rejects the false result using the alternative model's zero remainder.
The integer-only global populations in those controls follow the prior retirement
decision. `authority_callback_count_refinement.md` retains actual Count coverage
at the checked final-implication boundary, and
`authority_callback_count_model_local.md` rejects evaluating the alternative
transition's count guarantee in Keep's unchanged population model.

`authority_named_import_creation.md` and its wildcard companion check direct
and nested births, fields, and retained occurrences. Missing-birth, missing-bound,
and false-total companions reject the corresponding obligations. The caller
consumption and wildcard consumption fixtures check exact deaths across nested
calls; the original lifecycle refusals now reach spent-instance reuse and false
count claims. Private creation retains a neighboring private member and explicit
memory preservation. Birth-then-death checks do not infer a positive entry count.
Authority-mode returns never select the legacy counted-population transition.

The recovery review maps the three saved migration frontiers as follows:

| Recovery frontier | Checked repository replacement |
| --- | --- |
| Owned-count authentication and freshness | `authority_owned_count_*` fixtures and authenticated contract-entry bound kernel checks |
| Predicate entry/current model and contained tokens | Authority predicate precondition positive/false-zero controls, snapshot/predicate fixtures, and contained-resource exchange checks |
| Named pool member lifecycle and private memory | `authority_pool_named_member_helper_consumption.md` verifies unchanged C; `authority_pool_member_transfer.md` retains the original never-green stack-body proposal as a precise implicit-storage refusal. `authority_named_import_cross_pool_transfer.md` verifies explicit private ownership and framed custody |
| Earlier local named/private-member probes | `authority_named_field_*` positives and authority, alias, overlap, duplicate-input, and premature-retirement refusals |

The migration no longer depends on uncommitted recovery state. Original archives
remain preserved, including unrelated C++ and snapshot experiments; those are
outside the Milestone 3 consumer inventory. The fork commit and this inventory
are sufficient to resume the migration elsewhere.

The milestone-three constant-quantity slice migrates
`let_bound_constant_quantity.md` and `fold_rejects_a_negative_quantity.md` to
authority semantics. The former retains the let-bound contract quantity and
an ordinary authority-bearing control; the latter retains both zero acceptance
and rejection of a negative coefficient with its missing nonnegative fact.
`fold_negative_quantity_legacy_control.md` retains the original signed-quantity
regression until the final legacy-removal milestone; its authority replacement
is `fold_rejects_a_negative_quantity.md`.
The symbolic-plus-unit boundary remains recorded in the migration issue.
The obsolete global unanchored count fixtures were removed by explicit design
decision. Scoped wildcard aggregation remains covered by authority fixtures.
`counted_distinct_populations_symbolic_entry.md` now uses authority semantics,
with separate authorities for its independent families and no bound on their
unobserved sum.

`resource_count_predicate_snapshot.md` also uses authority semantics: an
ordinary control owns counter memory and authority, independently of reference
members. Its unchanged C retain operation restores a fresh predicate after the
checked member birth; the predicate's entry snapshot cannot substitute for
that updated relation.

`counted_resource_contribution_counter.md` selects authority semantics for all
seven functions. It separates empty contribution members from an ordinary
counter/authority control and supplies empty authority through storage. One
member is consumed per increment; exact-two callers consume their final member
and retire authority before returning memory. Whole symbolic cleanup and direct
zero/one/two-value pipelines preserve their original C and result guarantees.

`population_consumption_at_close.md` and
`population_consumption_wrong_increment.md` now use ordinary authority-bearing
controls. Explicit member consumption precedes invariant restoration; reopening
does not consume again. Nested calls and both reporting branches verify, while
the unchanged two-unit increment is rejected for failing the counter/count fact.

`authority_local_numeric_batch.md` covers a locally created concrete batch,
including zero changes and partial consumption. Concrete quantities use the
same custody ledger as units; kernel tests also preserve exact wildcard member
counts and check quantity-independent work. True symbolic-batch/unit mixing
is still a separate migration capability.

`a_population_count_is_not_a_wrapped_total.md` now selects authority semantics.
It retains all original C and count claims, supplies authority and the empty
entry population, and rejects the second two-billion birth at the checked
member transition. `authority_numeric_population_total.md` keeps the entire
original C while independently verifying the numeric caller's exact total of
seven. `authority_large_symbolic_population_total.md` admits the first large
symbolic birth; the numeric maximum/overflow pair admits the exact signed
maximum and rejects a further birth. These use the existing checked engine.
The overflow negative alone does not establish repeated symbolic-birth support;
that capability is covered by the later repeated-birth slice. The scalar logical
callback controls, named lifecycle effects, and recovered-prototype review are
completed by the closing slice below.

`authority_exact_symbolic_population_total.md` retains the original C and
verifies two births whose variable quantity is exactly one billion. The checked
ledger resolves that recorded equality through an indexed lookup and accounts
for both births numerically; a range alone cannot select a quantity. Its
missing-authority and wrong-total companions remain negative.
`authority_exact_symbolic_batch_partial_spend.md` transfers and consumes one
exactly known numerical batch while retaining the other; its overconsumption
companion rejects a third spend. Imported genuinely symbolic custody keeps its
representation. `authority_symbolic_birth_composition.md` now covers repeated
symbolic births within one helper: each addition has a checked non-wrapping
current total, the same actor retains custody, and the helper returns the
complete coalesced batch through the checked call engine. Negative controls
reject a missing bound, missing authority, and a false total. A kernel
regression checks the exact return, double transfer, unsupported partial
transfer, another actor's custody, and deterministic work with 16/64/256
unrelated facts and populations. This does not admit splitting a coalesced
symbolic batch, extending imported entry custody, or separate helper births
while the caller frames an earlier symbolic batch.
`authority_symbolic_batch_retirement.md` passes the whole returned symbolic
batch to a consuming helper and proves the caller's population returns to zero.
Retirement requires authority and exact complete-batch custody, cancels only
that birth delta, and rejects partial or repeated consumption. Its false-total
control remains negative; the same deterministic kernel regression checks
retirement across the three unrelated-state sizes.
Kernel regressions check custody, overflow, negative quantities, the range-only
boundary, and lookup work beside 16/64/256 unrelated facts and populations.
The existing maximum-count increment negative now reports
`PopulationCountOverflow` at its unchanged second call, rather than a missing
member or prerequisite diagnostic.

`population_count_states_its_transition.md` and
`population_count_across_a_produces_transition.md` now select authority semantics
and explicitly create the produced member. The real count transition verifies;
a fixed post-count of one remains rejected. The initializer and ordinary caller
in `produced_population_count_in_ensured_predicate.md` now receive explicit
authority for an empty entry family. Their ensured predicate observes checked
births, including the zero-quantity branch, with unchanged C.

The `authority_owned_count_*` fixtures cover contract-entry lower bounds from
authenticated member custody. A directly owned member and matching authority
entail a lower bound, including through an ordinary helper, without assuming
an exact global total. Checked consumption preserves nonnegativity and rejects
reuse of the earlier bound. Member ownership without authority cannot supply
these count facts. A kernel regression distinguishes authenticated custody
from a resource fact inserted without ledger membership.

`predicate_without_count_ignores_resource_population.md` now selects authority
semantics. The unchanged helper exchanges its owned cell for a member using
explicit empty-family authority. Its existing memory predicate remains valid
through the checked birth. Private member facts retain the current verification
model while evaluating only the member's own body; ambient memory ownership
cannot satisfy a missing body permission. A kernel regression checks bounded
work beside increasing numbers of unrelated caller locals.

`consumed_population_count_in_ensured_predicate.md` now uses authority semantics.
An ordinary accounting control owns the C fields and the slot/item authorities;
slot members remain separate. Explicit symbolic consumption and the unchanged
C subtraction restore the current `valid_capacity` predicate. The companion
`consumed_population_predicate_rejects_missing_consumption.md` rejects updating
capacity without performing the declared consumption, because the control
cannot be closed with its count equation restored.

The `authority_predicate_precondition_*` regressions preserve authenticated
authority counts when an entry predicate, including a nested predicate,
captures the resource model. The positive proves that a positive population
implies a positive unchanged counter; the negative refuses a false zero
counter. A snapshot keeps the immutable count ledger and count read witness,
without exposing execution custody or permitting population changes.
Count-independent predicates retain their identity across unrelated births.
Definition registration checks count dependencies, and a deterministic
multi-size regression checks linear work over the definition body.
The consumed-predicate proof uses an explicit, checked subtraction lemma that
returns both the post-state equality and the recomposed sum's definedness;
its original C and contract conditions remain unchanged.

`population_consumption_missing_contract.md`,
`population_consumption_nested_overconsume.md`, and
`population_consumption_repeated.md` now select authority semantics. Their
ordinary controls restore counter facts after checked member spends, but the
return checker rejects the missing promised member. The three unchanged C
programs retain their missing, nested-extra, and repeated-consumption refusals.

`population_cleanup_rejects_partial_quantity.md` now uses authority semantics.
Consuming two of three members while retaining the cleanup control violates
its counter/count equation. `population_cleanup_consumes_whole_quantity.md`
uses the same C and verifies after exposing the control and consuming all three.
The authority model permits partial consumption when the retained invariants
are restored; this negative rejects the mismatched cleanup equation.

`resource_population_open.md`, `population_open_calls_explicit_piece.md`,
and `population_call_with_restored_body.md` now select authority semantics.
An ordinary control owns counter memory and authority; scoped opening preserves
population membership while explicit-piece and whole-control helper calls
restore the required custody. The unchanged-C companions
`call_inside_open_population_does_not_assume_its_body.md`,
`population_call_requires_closed_body.md`, `population_call_rejects_open_alias.md`,
`population_call_rejects_reentrant_restored_body.md`,
`population_rejects_nested_open.md`, and `population_rejects_nested_alias_open.md`
reject false invariant certification or duplicating a suspended control.

`population_call_drops_the_cached_body_cell.md` and
`population_call_keeps_what_it_may_and_drops_the_body_cell.md` now select authority
semantics. The unchanged retaining helper explicitly births one member while
its ordinary counter/authority control is open. The caller proves its cached
pre-call value equals the new count minus one; the arbitrary-result companion
is rejected. The unrelated-call control also verifies restoration from saved
caller memory without the callee assuming its suspended invariant.

`return_population_rejects_missing_increment.md`,
`return_population_rejects_missing_ownership.md`,
`return_population_rejects_unupdated_sibling.md`, and
`return_population_rejects_wrong_release.md` now select authority semantics.
Three refuse restoring the exact counter/count equation after an explicit
checked lifecycle change; the missing-write case has count authority and a
read view, but is refused the unchanged C store. No post-count promise grants
write ownership or another control invariant. All four C programs are unchanged.

`load_origin_first_seen_per_function.md` now selects authority semantics.
Initialization receives empty slot authority and explicitly creates its capacity
batch while keeping pool memory owned separately. Reset preserves membership
without requiring authority; callers retain their own authorities. Both the
zero-capacity reset pipeline and the two-pool initializer preserve their
original C and postconditions, including the first pool's count predicate
across the second pool's call. Verification and expansion audit cover all four
functions; reordering the sidecar declarations also preserves the verdict.

`resource_pattern_counts_cross_contracts.md` now uses authority semantics for
all three original C functions. Each membership privately owns an abstract
availability token, which checkout consumes and return restores. Return accepts
arbitrary totals and uses the member's checked wildcard lower bound for the
unchanged C decrement. A checked helper birth may be followed by consumption
of that exact current member, restoring the arbitrary entry total. Kernel
regressions check exact token transfer, missing or duplicated children, wrong
member identity, and repeated consumption. The other-pool negative rejects
using unrelated member custody to bound a wildcard total. Verification and all
nine expansion-audit sites pass.

`resource_count_observe_witness.md` now selects authority semantics and retains
both original C functions and their one-member/symbolic-quantity lower bounds.
The checked observation names only count and quantity bounds, preserving the
immutable ledger, memory, and member custody without projecting private bodies.
Unary contract imports retain the exact owned batch while leaving the global
total arbitrary. New regressions cover zero quantity, missing authority, closed
private memory, and refusal to infer an exact total from symbolic custody.
Kernel checks reject unrelated facts and resource deltas and measure bounded
work beside increasing amounts of unrelated state. Both proofs and all four
original expansion-audit sites pass.

The `authority_named_import_*` group adds unary and wildcard authority plus named-member
preserving contracts. Entry total stays arbitrary; named instance identity and
fields remain in ordinary checked custody, with no anonymous quantity imported.
Two equal-argument members preserve different field values across a call, and a
forward-declared List-valued function preserves its Count observation. The import
ledger recovers checked schemas through an immutable indexed map. Negatives
reject absent authority, invented exact totals, and unsupported named lifecycle transfers.
Kernel checks cover unchanged resource context, refused quantity/instance
exchanges, authority transfer and return, and deterministic lookup scaling.
Wildcard preserving helpers retain both aggregate and exact Count observations,
including equal-argument members and ownership framed by the caller. Negatives
reject invented aggregate/exact totals, another anchor, duplicate binders, absent
authority, and imported lifecycle changes. Both import shapes have deterministic
lookup scaling checks. Unary consumption inside a standalone helper is supported as described below.
The closing slice supports named creation, wildcard lifecycle effects, and
caller-side lifecycle transfers. Assumed named lifecycle interfaces remain
unsupported because they supply no body certificate for that population effect.

The `authority_external_named_*` group exercises preserving assumed interfaces.
External and named callback preparation now receives the selected resource mode;
it does not build a legacy entry inside an authority project. Explicitly borrowed
authority, named identity and fields, aggregate/exact wildcard counts, and a
List-valued count function use the existing checked call boundary. Assumed
interfaces cannot create or consume named members or replace their identity.
Negatives reject missing authority, duplicate member maps, another anchor, and
named consumption. These are external contract assumptions, not proofs of an
external C body. The callback regression uses a pointer anchor; the scalar logical controls now select authority with ordinary explicitly
selected models and unchanged C signatures. Caller-side imported lifecycle
transfers are checked by the closing slice.

`population_symbolic_increment_bounded.md` and
`population_symbolic_increment_overflow.md` now select authority semantics.
Their original C and claims are retained: a symbolic helper birth followed by
a unit birth proves `count == n + 1` when bounded and rejects the second
addition when overflowing. Count observations and contract effects retain both
deltas. Numerical fragments keep separate checked custody from the symbolic
batch, including helper transfer and consumption. Companion regressions cover
an arbitrary entry total and refusal to drop the unit delta; kernel regressions
cover custody, repeated spend, missing authority, and deterministic scaling.
Regrouped signed sums require all three addition domains at certification.

Unary named consumption at standalone helper entries now records the exact
consumed identities and a relative death count. The new
`authority_named_import_consumption.md` fixture consumes two occurrences without
asserting that they exhaust the imported population. Neighboring fixtures
check unfolds before and after C execution, checked body facts, and preservation
of a framed member. Return-rewrite certificates independently recheck the
rewrite direction, facts, and ledger. Wrong-total, closed-authority, and
missing-death controls reject false totals, missing authority, and unchecked
consumption. Kernel
coverage checks successor identity, duplicate death, distinct equal-field
occurrences, no anonymous custody, and deterministic work alongside
16/64/256 unrelated imports. The closing slice extends this to named creation,
wildcard lifecycle changes, and caller-side transfers. The original unary
helper-call refusal retains its C and now reaches reuse of the spent occurrence.

### Milestone 4: mutex-held authority controls

**Chunk 1, deposit and acquisition:** This chunk adds a capability and
migrates no legacy group. Authority mode now admits the four modeled mutex
calls; thread creation and join remain refused until milestone 6. A control
that owns its counter cell and `authority(reference(obj))` declares a proof
field, so it is a named instance. Its fold and unfold use the ordinary
named-instance exchange, which now admits one contained authority in
authority mode; the certificate checker requires the creation ledger to be
unchanged. Initialization deposits that control without selecting
counted-population custody, lock returns it, and unlock requires it folded
with its facts true at the current total.

Positive: `authority_mutex_control_deposit.md` (establish, deposit, lock, member
birth with a count observation, unlock, destroy, spend, retire, free) and
`authority_mutex_control_sequential.md` (the same control without a mutex).
Negative: `authority_mutex_control_unlock_open_rejected.md`,
`authority_mutex_control_bad_increment_rejected.md`,
`authority_mutex_member_alone_rejected.md`,
`authority_mutex_control_wrong_mutex_rejected.md`,
`authority_mutex_control_stale_initialization_rejected.md`, and
`authority_control_instance_duplicate_authority_rejected.md`. The kernel test
`authority_mode_publication_takes_no_population_custody` checks publication,
acquisition, release, and destruction. `click verify` and `click audit` pass
on the deposit fixture, and the audit expands and reverifies its three smart
sites.

**Chunk 2, acquiring and releasing helpers:** This chunk also adds a
capability and migrates no legacy group. Authority mode admits the classified
mutex helper contract when it has exactly one preserved typed `mutex_use`, one
produced or consumed guard, and the matching protected state. The caller
applies the checked runtime exchange; the helper's own proof cannot open the
acquired control, so it changes no population. The protected footprint
derivation now treats a contained authority as owning no bytes.

Positive: `authority_mutex_control_helpers.md` (two critical sections through
the helpers; the second observes the current count, spends the member, and
restores the control). Negative:
`authority_mutex_control_helper_stale_count_rejected.md`,
`authority_mutex_control_helper_missing_state_rejected.md`,
`authority_mutex_control_helper_wrong_mutex_rejected.md`, and
`authority_mutex_control_helper_open_rejected.md`.

**Chunk 2 follow-up, locked helpers:** A standalone helper may now open the
control it acquires. The typed lock enters the control's population into the
helper's proof once, with a fresh total bounded below by the members the
helper owns and no creator right. A locked helper contract preserves one typed
`mutex_use` and declares at most one consumed or produced member of the
acquired population; at return, the checked births and deaths under the
acquired authority must match it exactly, read from the ledger after unlock
has returned the authority to the escrow. The caller lends the escrowed
population to the call in its ledger and applies the declared effect on
return. The wildcard-consumption check from
`authority-establishment-review.md` defers acquired populations to this check.

`authority_mutex_control_helper_open_rejected.md` becomes
`authority_mutex_control_helper_open.md` (pass) with its C and proof
unchanged: the helper's observation of a fresh total that it does not change
is sound, and the new negatives below protect the population instead.
Positive: `authority_mutex_locked_release.md` (a locked release that spends
its caller's member; the creator observes zero after destruction). Negative:
`authority_mutex_locked_release_unspent_rejected.md` (declared death never
spent), `authority_mutex_locked_release_other_population_rejected.md` (member
of a population the helper never acquired),
`authority_mutex_locked_release_stale_rejected.md` (the caller's counter fact
from before the call), `authority_mutex_locked_undeclared_birth_rejected.md`
(a birth with no `produces`), and
`authority_mutex_locked_reacquire_rejected.md` (a second acquisition in one
proof). An unconditional locked retain remains open: creating a member under
a fresh total needs a bound that rules out counter overflow.

**Chunk 3, protected bodies and local conservation:** Six fixtures leave the
legacy path; each also drops `guarded_by`, since initialization supplies the
association.

- `mutex_population_body_helper.md` and `mutex_population_body_view_helper.md`
  (pass), `mutex_population_body_missing.md` (fail: missing `owns
  p[10..12]`), and `mutex_population_body_missing_direct.md` (fail: missing
  `views p[10..11]`) select authority with unchanged C, proofs, and
  outcomes. Each holds a `contribution` unit beside a typed protected
  counter; the unit still grants no protected memory.
- `population_conservation_local_mutex.md` (pass) keeps its C and `twice`
  result of two. The legacy body that owned the counter and counted its own
  units becomes a field-bearing control that owns the counter and
  `authority(remaining(p))` and states `p->value == 3 - count(remaining(p))`.
  `contribute` borrows the authority and counter, folds the control, deposits
  it at initialization, spends one unit and increments under the lock, and
  must restore the equation before unlock. `twice` creates the three units
  under its borrowed authority and spends the last.
- `population_conservation_local_mutex_bad_increment.md` (fail) keeps its
  increment by two; restoring the control fails on the conservation
  equation, fact 3 of 3.

`mutex_population_separate_body.md` and
`mutex_population_missing_value_relation.md` stay on the legacy path: their
contributions are consumed by `pthread_create` workers, which authority mode
refuses until milestone 6. They move to milestone 6 chunk 3.

**Chunk 4, held and unheld helpers and closeout:** The seven
`population_mutex_*` fixtures leave the legacy path with their C unchanged.
The legacy member body that owned the counter and stated its own count
becomes a field-bearing control that owns the counter and
`authority(member(p))` and states `p->value == count(member(p))`. The caller
borrows an arbitrary population with zero members, creates three members,
and deposits the control. `read_member` borrows the authority and the
counter, and states that it leaves the counter unchanged.

- `population_mutex_helper_held.md` (pass): under the lock, the helper
  observes the count of three, and the control is restored before unlock.
- `population_mutex_helper_unheld.md` (fail: `Requires owns
  authority(member(...))`) and `population_mutex_direct_read_unheld.md`
  (fail: missing `views p[10..11]`): without an acquisition, the control and
  its counter stay in the mutex.
- `population_mutex_cleanup_held.md` (fail: `Requires owns
  authority(member(p))`): spending members after unlock and before
  destruction needs the escrowed authority.
- `population_mutex_hidden_unit_at_release.md` and
  `population_mutex_incomplete_publication.md` (fail: the claimed count of
  two does not hold): a member hidden in another wrapper is still counted.
- `population_mutex_second_custodian.md` (fail: `Requires owns
  authority(member(...))`): depositing the control in a second mutex removes
  it from the first critical section.

The legacy refusal messages about complete custody and a second custodian
no longer appear: authority makes each condition an ordinary ownership or
count fact. `mutex-resource-contracts.md` marks the legacy custody rule for
deletion in milestone 7. Milestone 4's exit gate holds: lock gives control
ownership, unlock requires its restored invariant, a member alone cannot
expose it, and no authority proof uses counted-population custody.

### Milestone 5: retire `guarded_by` associations

**Chunk 1, core association semantics:** Ten fixtures drop `guarded_by` with
their C unchanged. Initialization now supplies each association.

- Nine keep their outcomes and messages unchanged:
  `guarded_resource_mutex_flow.md`, `modeled_pthread_mutex_parent_interference.md`,
  and `mutex_lifetime_named_runtime.md` (pass), and
  `guarded_resource_unlock_unfolded_rejected.md` (unfolded restoration),
  `modeled_pthread_mutex_early_destroy.md` (early destroy),
  `modeled_pthread_mutex_parent_interference_rejects_stale.md` (stale parent
  observation), `mutex_lifetime_named_stale_runtime.md` (stale
  initialization), `mutex_resource_quantity_requires_conservation.md`, and
  `mutex_unlock_missing_guard_and_invariant.md` (missing guard and state)
  (fail).
- `guarded_resource_wrong_mutex_rejected.md` refused publication because the
  annotation named a different mutex. Without the annotation, depositing
  `cell_state` in `cell->other` is an ordinary publication, so its unchanged
  C now fails because `wrong` returns with that mutex still live and holding
  the state. The wrong-association refusal moves to the new
  `mutex_association_wrong_mutex_rejected.md`: a helper's typed use of
  `cell->guard` cannot be supplied by the lifetime of `cell->other` (`Requires
  owns mutex_use(&cell->guard, cell_state(cell))`).

**Chunk 2, guard family:** The 27 `mutex_guard_*` fixtures that used
`guarded_by` drop it with their C, proofs, and expectations unchanged. Each
already deposits its state at a named initialization, so the annotation
added no association. All keep their checked-in outcomes and messages: 9
pass and 18 fail, including the preserving-contract, incomplete-fold,
missing-guard, live-acquisition, duplicated-guard, and missing-storage
refusals.

**Chunk 3, use, helper-transfer, and runtime-contract families:** The 10
`mutex_use_*`, 3 `mutex_helper_transfers*`, and 6 `runtime_mutex_contract_*`
fixtures that used `guarded_by` drop it with their C, proofs, and
expectations unchanged. All keep their outcomes and messages: 6 pass and 13
fail. The failures include the wrong-type, untyped, missing-restore,
stale-acquisition, stale-call, stale-payload, and unlocked-read refusals, and
the six named-initialization contract refusals. The only remaining
`guarded_by` fixtures are the two worker `mutex_population_*` fixtures.

**Chunk 4, specification, documentation, and audit:**
`docs/concepts/resources.md` now teaches association by initialization with a
typed-use example. `docs/internals/mutex-resource-contracts.md`,
`docs/internals/concurrency-contracts-and-diagnostics.md`,
`docs/internals/resource-parameters.md`, and the concurrency design probe no
longer present the annotation as a current mechanism. The trusted
`src/languages/c/modeled_pthread_spec.md` states that initialization
associates the protected resource. It keeps one sentence marking `guarded_by`
deprecated, because the parser and kernel accept it until milestone 7. The
discovery search otherwise finds the annotation only in migration records,
the removal plan, and the two worker fixtures that move to milestone 6.

