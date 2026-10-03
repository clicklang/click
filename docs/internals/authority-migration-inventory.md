# Authority migration: consumer inventory

This is the consumer inventory for `issues/authority-migration.md`, not a specification of new syntax. The groups below use the legacy resource/population rules unless marked as authority-mode proofs. Design notes are proposals or historical investigations, not passing fixtures. The C in source-backed fixtures is frozen by the migration issue.

The authority-mode companion in `examples/bounded-pool-authority` references
unchanged C in the original project. It verifies initialization, checkout,
return, cleanup, growth, shrink, and transfer, plus the original zero-capacity, two-object, and
resize and transfer pipelines. Shrink consumes a symbolic owned slot quantity under the
control's authority while preserving the global remainder and checked-out
members. Growth produces only its requested slot quantity under the existing
control, preserves both populations' old members, and checks signed capacity
bounds. The original two-pool transfer also verifies through two ordinary
controls, preserving private object memory and restoring both invariants. Its
reduced four-unit exchange is
covered by `authority_four_effect_exchange.md`: all four authorities and exact
member effects are checked, neighboring ownership survives, and final cleanup
is exact. The original transfer pipeline now verifies through ordinary helper contracts. The
reduced `authority_two_control_init_call.md` checks initialization with an
independent caller-held control. Allocation reconciliation projects each
control using its actual owner's ledger, preserving caller authority and
population counts. `authority_two_control_birth_helpers.md` now checks two initializer calls
returning two controls and two independent unit slots. Each control preserves
its anchor and authority scopes; ordinary `open` supplies the memory-framing
facts for the intervening call. An extra-member regression rejects restoring
an invalid control invariant. The original transfer pipeline now also verifies, preserving the private value
and returning both controls, the destination member, and the source slot. Its
proof establishes memory separation by opening ordinary storage resources;
checkout's contract explicitly preserves the object's value. No C or syntax
changed. Switching the original project off legacy semantics is the next
checkpoint.

## Discovery boundary

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
The bounded-pool sidecar remains on its existing path; this group supplies
one prerequisite without migrating it.

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

The original bounded-pool sidecar still selects legacy semantics. Its migration
needs symbolic batch
forwarding, and the remaining resize/transfer/cleanup pipeline checks. The
roadmap in `issues/authority-migration.md` records these as
remaining dependencies; the new fixtures are partial progress, not evidence
that the original pipeline has migrated.

The following commands, run from the repository root, find the checked-in consumers when this inventory is updated. Review matches in context: C functions named `count`, prose mentioning quantities, and Rust variables named `count` are not population observations. The mdtest list is intentionally grouped below by proof dependency rather than by every syntactic occurrence.

```sh
rg -l '\bcount\s*\(' examples mdtests design docs src tests
rg -l '\bguarded_by\b' examples mdtests design docs src tests
rg -l '\b(owns|views|consumes|produces)\s+[^;\n]*\s+of\s+\w+\s*\(' examples mdtests design docs src tests
rg -l 'field.*count|count.*field|is_countable|CountedPopulation' examples mdtests design docs src tests
```

The third query finds explicit coefficient clauses, including unrelated resource quantities. Repeated `owns`/`consumes` clauses also encode quantities and require contextual review. The `count` search covers body facts, contracts, predicates, snapshots, and loop invariants; those are distinct authority-dependency sites, not one interchangeable test.

## Sequential refcount status

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

## Shared-parent migration status

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
`old(count(child_ref(p->kid))) > 1`, remains unsupported: deferred guard
certification refused Count ownership, and modular application refused the
explicit two-to-one quantity shape. These limitations are not claimed fixed.
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

## Source-backed example and design groups

| Group and current path | Checked-in files | Existing property to preserve |
| --- | --- | --- |
| Sequential refcount project; authority | `examples/refcount/refcount.click`, `examples/refcount/README.md` | Counter equals the reference population through initialize, retain, symbolic retain/release, nonfinal release, final free, allocation failure, and callers. A final release needs the final member and reclaims once. All six related positive count-contract fixtures also use authority. |
| Shared parent; authority | `design/shared-heap-probes/shared_parent.click`, `design/shared-heap-probes/README.md`, `design/shared-heap-probes/click.project.json` | Parent wrappers carry child references through attachment, detach, nested calls, both destruction orders, surviving-parent reads, and final reclamation. The frozen main C verifies eight functions and audits 48 smart sites; the related boundary fixtures pass the full repository gate. |
| Bounded pool; legacy | `examples/bounded-pool/bounded_pool.click`, `examples/bounded-pool/README.md` | `count(pool_object(pool, _))` is a per-pool wildcard total; exact objects and slot counts support checkout, return, resize, zero capacity, private object writes, and source-to-destination transfer. |
| Earlier authority design; non-executable | `design/concurrency-probes/shared-count-authority.md`, `design/concurrency-probes/explicit-authority.md`, `design/concurrency-probes/README.md` | Preserve the motivating hostile cases and protocol questions; these documents do not define the approved source interface. The migration issue supersedes the whole-population mutex-custody plan. |

`examples/jsonc-refcount/README.md` and the `mdtests/jsonc_refcount_{getter,increment,setter}.md` fixtures describe a separate JSON-C resource/model-field example; inspect them during the final source/doc audit, but their `count` search hits include ordinary C/API naming and should not be assumed to be Click population observations.

## Sequential mdtest dependency groups

Unless marked otherwise, these are legacy-path fixtures. In the refcount row,
`counted_resource_transfer.md`, `population_unit_needs_its_body.md`,
`counted_resource_refcount_transitions.md`,
`counted_resource_population_body.md`,
`counted_resource_population_lifetime.md`, and
`counted_resource_independent_populations.md` select authority semantics;
`counted_resource_rejects_minting.md`,
`counted_resource_rejects_double_spend.md`, and
`population_simple_exit_rejects_final_leak.md` select authority semantics;
`authority_conditional_release_transfer.md`,
`counted_resource_authority_retained_control.md` and the three
`authority_count_rejects_*.md` fixtures add checked authority regressions. The
paths in each row are relative to `mdtests/`. The pass/fail ledger below comes
from each fixture's checked-in `expect` block; names alone do not determine
the expected result.

All 18 fixtures in the shared-parent lifecycle row select authority semantics.
Their contracts and intended refusals pass the full repository gate; see the
verification and audit evidence above.

| Group | Files and preserved behavior |
| --- | --- |
| Refcount and exact population basics | `counted_resource_refcount_transitions.md`, `counted_resource_population_body.md`, `counted_resource_population_lifetime.md`, `counted_resource_independent_populations.md`, `counted_release_preserves_nonfinal_allocation.md`, `population_initialized_cleanup.md`, `population_unit_needs_its_body.md`, `population_simple_exit_rejects_final_leak.md`: exact count/body relation, independent populations, nonfinal allocation preservation, initialization/finalization, and refusal to leak or produce a unit without its body. `counted_resource_rejects_minting.md`, `counted_resource_rejects_double_spend.md`, `counted_resource_transfer.md` pin ordinary ownership transfer and spend, even where they do not spell `count`. |
| Quantity, arithmetic, patterns, snapshots | `counted_distinct_populations_symbolic_entry.md`, `counted_distinct_populations_symbolic_sum.md`, `population_symbolic_increment_bounded.md`, `population_symbolic_increment_overflow.md`, `population_cleanup_rejects_partial_quantity.md`, `fold_rejects_a_negative_quantity.md`, `let_bound_constant_quantity.md`, `resource_count_patterns.md`, `resource_pattern_counts_cross_contracts.md`, `resource_count_observe_witness.md`, `resource_count_predicate_snapshot.md`, `population_count_states_its_transition.md`, `population_count_across_a_produces_transition.md`, `c_contract_executes_resource_count.md`, `c_step_contract_resource_count_is_model_local.md`, `produced_population_count_in_ensured_predicate.md`, `consumed_population_count_in_ensured_predicate.md`, `predicate_without_count_ignores_resource_population.md`, `a_population_count_is_not_a_wrapped_total.md`: exact versus wildcard totals, bounded `int32` sums, nonnegative coefficients, contracts and predicates, historical snapshots, witnesses, and an unrelated predicate that must remain usable. |
| Open body, call, and return boundaries | `resource_population_open.md`, `population_open_calls_explicit_piece.md`, `call_inside_open_population_does_not_assume_its_body.md`, `population_call_with_restored_body.md`, `population_call_requires_closed_body.md`, `population_call_drops_the_cached_body_cell.md`, `population_call_keeps_what_it_may_and_drops_the_body_cell.md`, `population_call_rejects_open_alias.md`, `population_call_rejects_reentrant_restored_body.md`, `population_rejects_nested_open.md`, `population_rejects_nested_alias_open.md`, `load_origin_first_seen_per_function.md`, `return_population_rejects_missing_increment.md`, `return_population_rejects_missing_ownership.md`, `return_population_rejects_unupdated_sibling.md`, `return_population_rejects_wrong_release.md`: scoped restoration, no duplicated body access, call invalidation, and return checking. Some old positive body-open permissions must be replaced by ordinary ownership plus authority, while their memory and count claims remain. |
| Consumption at close and contribution | `counted_resource_contribution_counter.md`, `population_consumption_at_close.md`, `population_consumption_missing_contract.md`, `population_consumption_nested_overconsume.md`, `population_consumption_repeated.md`, `population_consumption_wrong_increment.md`: exact two, one spend across scope close/return, and refusal of missing, repeated, or incorrect consumption. |
| Shared parent lifecycle | `shared_heap_one_heap_parent.md`, `shared_heap_one_heap_parent_missing_child_ref.md`, `shared_heap_one_heap_parent_missing_retain.md`, `shared_heap_one_heap_parent_wrong_child.md`, `shared_heap_two_parent_branch_release.md`, `shared_heap_two_parent_branch_release_positive.md`, `shared_heap_two_parent_caller.md`, `shared_heap_population_lifecycles.md`, `shared_heap_population_certification.md`, `shared_heap_population_initialized_body_gap.md`, `shared_heap_composed_attach_detach.md`, `shared_heap_creator_release_repro.md`, `shared_heap_final_detach_repro.md`, `shared_heap_detach_old_resource_handoff.md`, `shared_heap_detach_leak_diagnostic.md`, `shared_heap_produced_ensure_transport.md`, `child_release_branch_on_count.md`, `parent_attach_call_frame.md`: parent-owned child membership, aliases, failed allocation, both destruction orders, preserved payload, and final free. Missing child/retain/wrong child and leak variants must still fail. |
| Loop and pure expression sites | `loop_old_count_invariant.md`, `loop_invariant_body.md`, `pure_click_functions.md`, `recursive_call_precondition_bounds_a_decremented_argument.md`, `recursive_call_precondition_refuses_a_decremented_lower_bound.md`, `recursion_measure_refusal_spells_its_measure_and_goal.md`: old versus current count in invariants and proof facts, predicate/pure-function evaluation, and diagnostics at recursive calls. |

The field-based legacy refusals are separate migration targets: `resource_fields_reject_count.md` and `resource_fields_reject_hidden_count.md` currently reject with `resource ... has fields and is not countable`. Under explicit authority, field-bearing members must become countable positive cases with retained identity. `resource_fields_reject_quantity.md` rejects even `1 of cell(p)` under that same classification; the migration must distinguish any remaining symbolic-quantity limitation from countability. `resource_field_child_equations.md`, `resource_field_child_equation_rejects_other_start.md`, and `resource_unfold_binds_children_and_fields.md` protect distinct field identity and child binding independent of count.

### Checked-in `expect` outcomes

The following **fail** fixtures are the negative side of the sequential groups above. Every other explicitly named sequential mdtest in those groups has a success `expect` block at baseline. Preserve each failing claim's underlying obligation even if the diagnostic changes with the new permission model.

| Group | Expected-failure files |
| --- | --- |
| Arithmetic, quantity, patterns, and proof-expression boundaries | `a_population_count_is_not_a_wrapped_total.md`, `counted_distinct_populations_symbolic_sum.md`, `fold_rejects_a_negative_quantity.md`, `population_cleanup_rejects_partial_quantity.md`, `population_symbolic_increment_overflow.md`, `population_count_across_a_produces_transition.md`, `c_step_contract_resource_count_is_model_local.md`, `recursion_measure_refusal_spells_its_measure_and_goal.md`, `recursive_call_precondition_refuses_a_decremented_lower_bound.md`. |
| Body and call boundaries | `call_inside_open_population_does_not_assume_its_body.md`, `population_call_drops_the_cached_body_cell.md`, `population_call_rejects_open_alias.md`, `population_call_rejects_reentrant_restored_body.md`, `population_call_requires_closed_body.md`, `population_rejects_nested_alias_open.md`, `population_rejects_nested_open.md`, `population_unit_needs_its_body.md`. |
| Population updates and return | `counted_resource_rejects_double_spend.md`, `counted_resource_rejects_minting.md`, `population_simple_exit_rejects_final_leak.md`, `population_consumption_missing_contract.md`, `population_consumption_nested_overconsume.md`, `population_consumption_repeated.md`, `population_consumption_wrong_increment.md`, `return_population_rejects_missing_increment.md`, `return_population_rejects_missing_ownership.md`, `return_population_rejects_unupdated_sibling.md`, `return_population_rejects_wrong_release.md`. |
| Parent identity and lifetime | `shared_heap_one_heap_parent_missing_child_ref.md`, `shared_heap_one_heap_parent_missing_retain.md`, `shared_heap_one_heap_parent_wrong_child.md`, `shared_heap_two_parent_branch_release.md`, `shared_heap_population_initialized_body_gap.md`, `shared_heap_detach_leak_diagnostic.md`, `resource_field_child_equation_rejects_other_start.md`. The unsuffixed two-parent branch fixture is a negative control; its `..._positive.md` counterpart is the passing claim. |
| Field classification | `resource_fields_reject_count.md`, `resource_fields_reject_hidden_count.md`, `resource_fields_reject_quantity.md`. The first two are explicit conversion-to-positive targets with authority. The third needs a separately stated quantity rule. |

## Concurrent and mutex mdtest groups

These are all legacy-path fixtures. The two worker families are intentionally separate: ordinary abstract accounting does not prove a protected C counter equality.

| Group | Files and preserved behavior |
| --- | --- |
| Abstract workers and joins | `modeled_pthread_counted_join.md`, `modeled_pthread_counted_reverse_join.md`, `modeled_pthread_counted_before_join.md`, `modeled_pthread_counted_join_stale.md`, `modeled_pthread_counted_neutral_pending.md`, `modeled_pthread_counted_pending_helper.md`, `modeled_pthread_counted_pending_wildcard.md`, `modeled_pthread_counted_overlap_rejected.md`, `modeled_pthread_thread_confined_resource_rejected.md`: worker transfer and join, failure to observe pending/stale counts, wildcard refusal, independent/reversed joins, and overlap/confinement rejection. |
| Shared abstract worker population | `modeled_pthread_counted_shared_join.md`, `modeled_pthread_counted_shared_forward_join.md`, `modeled_pthread_counted_shared_partial_then_create.md`, `modeled_pthread_counted_shared_retained.md`, `modeled_pthread_counted_shared_symbolic.md`, `modeled_pthread_counted_shared_neutral.md`, `modeled_pthread_counted_shared_observer.md`, `modeled_pthread_counted_shared_stale.md`, `modeled_pthread_counted_shared_early_count.md`, `modeled_pthread_counted_shared_missing_unit.md`: shared worker-ticket accounting, create failure, either join order, retained units, and early/stale/missing-unit refusals. These no-lock workers need an explicit authority protocol before migration; join cannot retroactively authorize a worker update. |
| Count and protected memory | `population_conservation_local_mutex.md`, `population_conservation_local_mutex_bad_increment.md`, `population_mutex_helper_held.md`, `population_mutex_helper_unheld.md`, `population_mutex_cleanup_held.md`, `population_mutex_direct_read_unheld.md`, `population_mutex_hidden_unit_at_release.md`, `population_mutex_incomplete_publication.md`, `population_mutex_second_custodian.md`, `mutex_population_separate_body.md`, `mutex_population_missing_value_relation.md`, `mutex_population_body_helper.md`, `mutex_population_body_view_helper.md`, `mutex_population_body_missing.md`, `mutex_population_body_missing_direct.md`: held/unheld helper access, complete publication/release, local conservation, exclusive custodian, and separation of contribution count from concrete counter value. The missing-value-relation case must continue to fail. |
| `guarded_by` positive and negative | `guarded_resource_mutex_flow.md`, `guarded_resource_unlock_unfolded_rejected.md`, `guarded_resource_wrong_mutex_rejected.md`, `modeled_pthread_mutex_early_destroy.md`, `modeled_pthread_mutex_parent_interference.md`, `modeled_pthread_mutex_parent_interference_rejects_stale.md`; plus `mutex_guard_*.md`, `mutex_use_*.md`, `mutex_helper_transfers*.md`, `mutex_lifetime_named*.md`, `mutex_resource_quantity_requires_conservation.md`, `mutex_unlock_missing_guard_and_invariant.md`, and `runtime_mutex_contract_*.md`. This is the complete `guarded_by` mdtest filename family at baseline (the glob families are finite and discoverable with the command above). Preserve authenticated protected-resource type and initialization identity, folded restoration, wrong-mutex/stale-state rejection, and mutex lifetime/use/guard behavior while removing the annotation. |

`guarded_by` also appears in `src/languages/c/modeled_pthread_spec.md` and the implementation paths named below. The plain mutex tests without the annotation remain neighboring controls for ordinary mutex transfer; they are not authorization to drop the guarded negative cases.

For the explicitly named concurrent fixtures, the **fail** `expect` blocks are: `modeled_pthread_counted_before_join.md`, `modeled_pthread_counted_join_stale.md`, `modeled_pthread_counted_neutral_pending.md`, `modeled_pthread_counted_pending_helper.md`, `modeled_pthread_counted_pending_wildcard.md`, `modeled_pthread_counted_overlap_rejected.md`, `modeled_pthread_thread_confined_resource_rejected.md`, `modeled_pthread_counted_shared_early_count.md`, `modeled_pthread_counted_shared_missing_unit.md`, `modeled_pthread_counted_shared_observer.md`, `modeled_pthread_counted_shared_stale.md`, `population_conservation_local_mutex_bad_increment.md`, `population_mutex_cleanup_held.md`, `population_mutex_direct_read_unheld.md`, `population_mutex_helper_unheld.md`, `population_mutex_hidden_unit_at_release.md`, `population_mutex_incomplete_publication.md`, `population_mutex_second_custodian.md`, `mutex_population_body_missing.md`, `mutex_population_body_missing_direct.md`, `mutex_population_missing_value_relation.md`, `guarded_resource_unlock_unfolded_rejected.md`, `guarded_resource_wrong_mutex_rejected.md`, `modeled_pthread_mutex_early_destroy.md`, `modeled_pthread_mutex_parent_interference_rejects_stale.md`, `mutex_resource_quantity_requires_conservation.md`, and `mutex_unlock_missing_guard_and_invariant.md`. Every other individually named concurrent mdtest above has a success `expect` block. For the `mutex_guard_*`, `mutex_use_*`, `mutex_helper_transfers*`, `mutex_lifetime_named*`, and `runtime_mutex_contract_*` families, inspect each `expect` block before migrating that family; both passes and refusals are present. The expected failures include unsuffixed `..._observer.md` and `..._cleanup_held.md`, so migration must not infer outcome from the filename.

## Kernel, surface, and documentation consumers

The kernel regression anchors are `src/kernel/tests/resource_tests.rs` (including `resource_field_schemas_are_typed_shared_and_non_countable`, population/count witness tests), `src/kernel/tests/contract_execution_tests.rs` (cross-contract population counts), and `src/kernel/tests/resource_scaling_tests.rs` (partition cost and alias refusal). Count-related tests also occur in `src/kernel/tests/{canonicalization,execution,iterated_ownership,loan_model,memory_reasoning,state_identity}_tests.rs` and `src/kernel/functions/callback_contract_tests.rs`; use the discovery commands before changing the kernel. The executable mechanism currently spans `src/kernel/primitives/counted_populations.rs`, `src/kernel/population_access.rs`, `src/kernel/proof/{population_initialization,population_consumption}.rs`, `src/kernel/resource_tracker/`, `src/kernel/mutexes/{population,invariant_interface,assumed_protocol}.rs`, and `src/kernel/primitives/contracts.rs`. Surface classification and lowering occur in `src/surface.rs`, `src/surface/parser.rs`, `src/surface/validation/{definition_validation,declaration_expansion}.rs`, and `src/surface/verification.rs`. These are code locations, not approved new semantics.

The existing `constructs`/`construct(...)` route is a separate establishment surface to review: parsing is in `src/surface/parser.rs`, declaration checks in `src/surface/validation/definition_validation.rs`, outcome application in `src/surface/proof/proof_object/step_application.rs`, and the checked operation in `src/kernel/functions.rs` through `src/kernel/api.rs`. It currently authorizes exactly one owned abstract token from a function contract, with duplicate-token rejection; it does not establish a population authority today.

Public explanations to revise as groups migrate are `docs/concepts/resources.md` (quantity, shared body, count, wildcard, worker reservation, `guarded_by`), `docs/reference/language/index.md` (resource syntax and semantics), `docs/reference/language/grammar.md`, `docs/reference/glossary.md`, `docs/reference/examples.md`, and `examples/README.md`. Source-backed internal explanations include `docs/internals/resource-invariants.md`, `docs/internals/resource-parameters.md`, `docs/internals/mutex-resource-contracts.md`, `docs/internals/concurrency-contracts-and-diagnostics.md`, `docs/internals/resource-tracker.md`, `docs/internals/kernel.md`, and `docs/internals/separation-logic.md`. `docs/concepts/loops-and-invariants.md`, `docs/concepts/pure-functions.md`, and `docs/concepts/predicates.md` cover count-bearing proof-expression contexts. Search other docs with the commands above at the final default switch; a documentation example can be a consumer even when no standalone mdtest file has the same name.

## Path ledger for later checkpoints

The refcount project, shared-parent project, and their migrated fixtures
identified above select authority semantics; the remaining rows are legacy. The intended order is refcount
fixtures, parent, field-bearing/wildcard and pool, mutex custody, then abstract
worker accounting. For each row, record the new fixture or unchanged migrated
source proof, its positive claim, its corresponding rejection, the selected
verification path, and verify/expand/audit evidence before removing it from
legacy. The final switch must also inspect imported summaries, caches, and
certificates; a successful new proof must never retry through legacy consumers.
