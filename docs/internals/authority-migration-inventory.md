# Authority migration: consumer inventory

This is the consumer inventory for `issues/authority-migration.md`, not a specification of new syntax. The groups below use the legacy resource/population rules unless marked as authority-mode proofs. Design notes are proposals or historical investigations, not passing fixtures. The C in source-backed fixtures is frozen by the migration issue.

The original `examples/bounded-pool` project now uses authority semantics.
All eleven original C functions and five arithmetic lemmas verify, including
symbolic growth/shrink, private writes under a closed control, cleanup, and the
zero, resize, two-object, and transfer pipelines. The C files are unchanged.
Initialization receives empty authority explicitly; cleanup retires both empty
populations. Exact member custody remains independent of global count facts.
The former authority companion has been consolidated into the original project.
Milestone 1 is complete: the full gate passed all 4,720 unit/integration and
190 fixture tests, and all 99 pool expansion-audit sites passed.

## Discovery boundary

The `authority_named_field_*` fixtures add local field-bearing families with
exact and wildcard authority. Occurrences with equal arguments retain distinct
identities and proof fields; aggregate/exact counts track local birth and
consumption. Disjoint private bodies can be updated through preserving ordinary
helper contracts while the caller's authority control remains closed.
Negatives cover overlapping memory, duplicate helper inputs, missing authority
for counts or lifecycle changes, late establishment, and premature retirement.
Named-member helper creation/consumption with explicit authority, heterogeneous
symbolic instance batches and general sums over fields remain outside
the implemented boundary. List-valued field descriptions are covered by the
Milestone 3 slice below. Milestone 2 is complete
for this boundary: the full gate passed 4,723 unit/integration tests and 190
fixture tests; all 48 new named-member expansion-audit sites passed.

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

The original bounded-pool sidecar has completed its authority migration;
the milestone-one status at the start of this inventory supersedes the earlier
partial checkpoints above.

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
| Bounded pool; authority | `examples/bounded-pool/bounded_pool.click`, `examples/bounded-pool/README.md`, `examples/bounded-pool/click.project.json` | `count(pool_object(pool, _))` is a per-pool wildcard total; exact objects and slot counts support checkout, return, resize, zero capacity, private object writes, and source-to-destination transfer. |
| Earlier authority design; non-executable | `design/concurrency-probes/shared-count-authority.md`, `design/concurrency-probes/explicit-authority.md`, `design/concurrency-probes/README.md` | Preserve the motivating hostile cases and protocol questions; these documents do not define the approved source interface. The migration issue supersedes the whole-population mutex-custody plan. |

`examples/jsonc-refcount/README.md` and the `mdtests/jsonc_refcount_{getter,increment,setter}.md` fixtures describe a separate JSON-C resource/model-field example; inspect them during the final source/doc audit, but their `count` search hits include ordinary C/API naming and should not be assumed to be Click population observations.

## Sequential mdtest dependency groups

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
Repeated births without an exact numeric quantity remain unsupported even for
bounded totals, so the
overflow negative is not evidence of that capability. Only the two scalar
logical callback controls in the sequential inventory still use legacy mode;
named body-opening/lifecycle effects and recovered-prototype review remain
unfinished.

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
reject absent authority, invented exact totals, and named lifecycle changes.
Kernel checks cover unchanged resource context, refused quantity/instance
exchanges, authority transfer and return, and deterministic lookup scaling.
Wildcard preserving helpers retain both aggregate and exact Count observations,
including equal-argument members and ownership framed by the caller. Negatives
reject invented aggregate/exact totals, another anchor, duplicate binders, absent
authority, and imported lifecycle changes. Both import shapes have deterministic
lookup scaling checks. Body opening, birth/consumption through helpers, and
external named lifecycle contract interfaces remain unsupported.

The `authority_external_named_*` group exercises preserving assumed interfaces.
External and named callback preparation now receives the selected resource mode;
it does not build a legacy entry inside an authority project. Explicitly borrowed
authority, named identity and fields, aggregate/exact wildcard counts, and a
List-valued count function use the existing checked call boundary. Assumed
interfaces cannot create or consume named members or replace their identity.
Negatives reject missing authority, duplicate member maps, another anchor, and
named consumption. These are external contract assumptions, not proofs of an
external C body. The callback regression uses a pointer anchor; the original
scalar logical callback controls remain legacy. Imported body opening and
lifecycle effects remain unsupported.

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

List-valued named members now use checked algebraic schemas under authority. `authority_named_list_field_private_helper.md` preserves two distinct `List<int32>` models across a private-memory helper while authority is closed, then observes aggregate counts under exposed authority; companion negatives reject counts without exposed authority and a mismatched field type. Early protected-type expansion and later member lowering share one checked schema resolver. `resource_fields_reject_quantity.md` now selects authority semantics and rejects anonymous quantities for missing separately named fields, rather than claiming the family is uncountable. The original `resource_fields_reject_count.md` and `resource_fields_reject_hidden_count.md` now select authority and have converted to positive outcomes. The first retains `count(cell(p)) == 1` as an external precondition, adds explicit authority and named custody, and exercises a heap caller with sealed private memory, List model preservation, and cleanup. The second retains its forward-declared List-valued count function with explicit constructor type arguments. `authority_field_count_function_call.md` exercises the function before and after the same external call; fresh unfoldings use exposed authority. Companion negatives reject direct/hidden observations and external calls under a closed control, including a fresh unfolding after a prior authorized count. The reader contract is an external assumption, not verification of an absent C body. Imported named body opening and lifecycle effects remain unfinished. Unary and wildcard preserving authority imports are supported, as described above. `resource_field_child_equations.md`, `resource_field_child_equation_rejects_other_start.md`, and `resource_unfold_binds_children_and_fields.md` protect distinct field identity and child binding independent of count.

### Checked-in `expect` outcomes

The following **fail** fixtures are the negative side of the sequential groups above. Every other explicitly named sequential mdtest in those groups has a success `expect` block at baseline. Preserve each failing claim's underlying obligation even if the diagnostic changes with the new permission model.

| Group | Expected-failure files |
| --- | --- |
| Arithmetic, quantity, patterns, and proof-expression boundaries | `a_population_count_is_not_a_wrapped_total.md`, `fold_rejects_a_negative_quantity.md`, `population_cleanup_rejects_partial_quantity.md`, `population_symbolic_increment_overflow.md`, `population_count_across_a_produces_transition.md`, `c_step_contract_resource_count_is_model_local.md`, `recursion_measure_refusal_spells_its_measure_and_goal.md`, `recursive_call_precondition_refuses_a_decremented_lower_bound.md`. |
| Body and call boundaries | `call_inside_open_population_does_not_assume_its_body.md`, `population_call_drops_the_cached_body_cell.md`, `population_call_rejects_open_alias.md`, `population_call_rejects_reentrant_restored_body.md`, `population_call_requires_closed_body.md`, `population_rejects_nested_alias_open.md`, `population_rejects_nested_open.md`, `population_unit_needs_its_body.md`. |
| Population updates and return | `counted_resource_rejects_double_spend.md`, `counted_resource_rejects_minting.md`, `population_simple_exit_rejects_final_leak.md`, `population_consumption_missing_contract.md`, `population_consumption_nested_overconsume.md`, `population_consumption_repeated.md`, `population_consumption_wrong_increment.md`, `return_population_rejects_missing_increment.md`, `return_population_rejects_missing_ownership.md`, `return_population_rejects_unupdated_sibling.md`, `return_population_rejects_wrong_release.md`. |
| Parent identity and lifetime | `shared_heap_one_heap_parent_missing_child_ref.md`, `shared_heap_one_heap_parent_missing_retain.md`, `shared_heap_one_heap_parent_wrong_child.md`, `shared_heap_two_parent_branch_release.md`, `shared_heap_population_initialized_body_gap.md`, `shared_heap_detach_leak_diagnostic.md`, `resource_field_child_equation_rejects_other_start.md`. The unsuffixed two-parent branch fixture is a negative control; its `..._positive.md` counterpart is the passing claim. |
| Field classification | `resource_fields_reject_quantity.md` rejects anonymous quantities requiring separately named members. `authority_field_count_direct_missing_authority.md`, `authority_field_count_function_missing_authority.md`, and `authority_field_count_external_missing_authority.md` reject observations or calls without exposed authority. The former direct/hidden count refusals have converted to positives with these permission controls. |

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
