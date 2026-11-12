# Smart tactics: fast checking and enforceable search boundaries

Priority: P1.

Soundness: not soundness. This is a checking-cost and search-boundary audit.
Removing automatic reasoning must preserve ownership, aliasing, initialization,
width, lifetime and provenance refusals; inability to prove separation is not
permission to write or preserve a value.

## Goal and audit boundary

A simple checking operation costs its explicit input and necessary state delta,
up to indexing factors. With those fixed, more ambient facts, owners, aliases,
loans, cached observations or execution history must not make it slower.
Expensive discovery belongs in budgeted, expandable search, whose expanded
steps satisfy the same checking rule. A fast special case does not establish
this guarantee for an operation's other routes.

The operation inventory starts from the `c53645952` baseline (2026-11-11,
PR #2520); the frozen dependency counts below reflect the current interface split.
It organizes the next measurements; it is not a claim that all checking paths
have been audited, or that every candidate below is a reproduced defect.
The interface refactor now exposes discovery through `kernel::search::ProofSearch`
without changing its behavior. The frozen
[dependency inventory](../build_support/proof_search_edges.tsv) records existing
callers and separates operation dependencies from the explicit `ProofDriver`
and mixed callers classified in the [caller audit](../design/proof-boundary-classification.md). The driver owns proof interpretation and the
choice between explicit obligation proofs and implicit solving. The
operation-to-driver migration list is now empty;
implicit solving by the driver is legitimate expandable work. No new scaling measurements accompany that split.
Existing test names below identify evidence to retain and inspect, not new
measurements. The contract lives in [Verifier design](../docs/internals/verifier-design.md)
and [Verification efficiency](../docs/internals/verification-efficiency.md).

The scope includes checking called by `step()`, explicit tactics, certificates,
entry setup, joins and completion. The implicit closer is separate from step
checking even when a bare step invokes it. Arithmetic premise discovery in
`solve` or that closer is legitimate search if budgeted and expandable;
applying its explicit certificate is checking. Trace printing, independent
expansion audits and debug-only cross-checks are distinguished from ordinary
checking, not counted as production scans merely because they iterate.

An index is not by itself a complexity argument. Enumerating a large bucket,
equality class or chain can still be ambient search. Nor may an implementation
justify eager derived facts or cache rebuilding by calling them output: the
delta must be required by the selected rule. Amortized claims need a total-work
argument across repeated steps and persistent forks, as well as cold misses.

## Reading the inventory

- **Scoped evidence:** named tests cover particular routes and growth axes;
  this does not certify the whole operation.
- **Source candidate:** a growing traversal exists on an identified path;
  a complete-operation red curve is still required before choosing a fix.
- **Reachability gap:** a helper scans, but its supported source caller or
  producer has not been established.
- **Coverage gap:** a path or growth axis has not been established by this pass.
- **Deferred evidence:** another roadmap owns a previously identified problem;
  its old counts are not fresh measurements. Existing priority stays unchanged.

There is no defensible total bug count yet. Rows are operations, not bugs;
several rows share helpers and a row can contain multiple routes. The previous
six-group estimate covered only resource/loan candidates, not the verifier.

## Reconciled status and ownership

The frozen inventory has **637 reference records**: 6 legacy bridges, 21 callers
of those bridges, 6 operation references, 0 operation-to-driver references,
16 mixed references, 122 driver references, 458 search references, 6 presentation
references and 2 imports. These are neither independent walks nor
runtime invocation counts. The [caller audit](../design/proof-boundary-classification.md)
classifies every mixed and operation-to-driver record and groups all 6
operation references. Registering the signed-definedness and unsigned-order
helpers exposes four existing search-only caller records; it adds no runtime work.

- **Confirmed architectural exceptions:** explicit legacy transport invokes
  discovery.
  T5 also retains uncharged transition-assumption reconstruction. No fresh
  scaling curve was run for this reconciliation.
- **Unmeasured candidates:** six kernel bridges map to four groups, L1, R2,
  F1 and C1. Other transition and declaration checks
  need caller-specific evidence. Preserve these as candidates, not confirmed
  performance regressions.
- **Legitimate search:** driver-owned implicit solve and explicit smart
  planning. Generating obligations is fast work; solving them may be slow and
  expandable. Have/claim and resource-scope obligation scheduling, step/fold dispatch,
  and retained step/fold completion are no longer open extractions.
- **Transport coverage:** T1–T5 below describe remaining routes. Scalar
  conjunction selection/regrouping and matching compound/nested implications
  with scalar leaves have ordinary expansion coverage. They do not settle
  non-scalar leaves, binders, other proof contexts or legacy retirement.
- **Separate owners:** the representation split in
  [unspellable facts](unspellable-facts.md) owns the remaining shared-term
  migration boundaries. Its original R1–R7 reproductions are closed; use its
  current closure checklist for remaining work. Those identifiers are local to
  that document, not this ledger's R1/R2. M1, E1 and Q1 retain the adjacent owners below.
- **Operation guards:** theorem application, scope completion, prepared-step
  publication and contract-claim opening have test-build discovery guards.
  Probes for have opening and statement preparation reproduce five operation/entry
  pairs through four existing bridge entries; see the [reproductions](../design/proof-boundary-classification.md#operation-discovery-guards-and-reproduced-crossings).
  Those two operations remain unguarded; no exception exempts their search.
- **Enforcement gap:** lexical dependency freezing and selected work counters
  do not prohibit every search call during expanded replay or detect arbitrary
  loops, shared-term export and copying. No global fast-proof guarantee yet.

Resource-scope completion now reports obligations to the driver, including
nested opens; function-exit deferral is unchanged. C-branch and proof-case script
interpretation now also lives in the driver; primitive split/focus/join operations
do not run arm-script callbacks. No operation-to-driver records remain in the frozen inventory.
For a new scaling experiment, L1 through an actual write remains a bounded
candidate. Boundary cleanup and enforcement are alternative next slices below.
Transport work should target a named T1–T5 route and its retirement criterion,
not accumulate more examples of an already-covered shape. These are separate
work items; this reconciliation changes no behavior.

### Remaining obligation generation

Step preparation retains emitted verification conditions and call preconditions,
and fold preparation retains its body facts, even when already known. The driver
proves each obligation with a written block or ordinary `solve`. This does not
finish evaluator migration: arithmetic operators still decide some safety
conditions before emitting any obligation. Replacing those decisions needs
round-trippable goals and flat generation/publication costs. The earlier, unlanded arithmetic-migration prototype failed `struct_array_element_expands_with_its_subscript`
(the initialized-global sum has no round-tripping overflow-goal spelling) and
`straight_line_assignments_cost_the_same_at_every_position` (work grows from
2765 to 2885 across twelve assignments). These are prototype findings, not
current failing tests; reproduce them when revisiting that migration. Retain
those controls for that slice.
The step/fold preparation migration is complete for the covered named,
population/authority, operational-wrapper and legacy-outcome routes. Keep its
no-reexecution, input-obligation and retained-endpoint invariants in
[the architecture](../docs/internals/architecture.md) and the scoped preparation
controls in `src/scaling_tests/surface/tests/tactic_tests/statement_steps.rs`.
Do not reopen those tasks under the broader lifecycle row E1.

Have/claim opening still uses the driver's `with_proved_lowering_requirements`
probe/reinvoke adapter. Solving belongs to the driver there; any repeated-lowering
cost needs its own fixed-input/ambient-growth measurement. This is not evidence
that the removed step/fold retry survives.


## Operation map

Paths in this table are relative to `src/`. Detailed outstanding measurements
follow it. None of these whole-operation rows is marked complete.

| Operation and intended cost | Checking entry points | Existing scoped evidence | Remaining evidence or candidate |
| --- | --- | --- | --- |
| Prepare selected code and function entry; pay once for selected declarations and clauses | `surface/verification.rs`, `kernel/functions.rs`, `kernel/termination.rs` | `surface/tests/step_shape_scaling_tests.rs`: `entry_setup_is_linear_in_owned_parameters`; `kernel/termination/termination_scaling_tests.rs`: call-chain, fan-out and cycle controls | Coverage gap: complete frontend/lowering/termination dependency map; no per-step rebuilding of prepared input. These are setup costs, not constant-size steps. |
| Execute a scalar statement or access; pay for selected expression and affected storage | `kernel/eval.rs`, `kernel/proof/execution.rs`, `kernel/primitives/memory_state.rs` | `kernel/tests/memory_scaling_tests.rs`: `one_store_is_logarithmic_in_unrelated_cells`, `sequential_owned_parameter_stores_ignore_earlier_cached_fields`; source step-shape tests | Memory/cache candidates M1; ownership and loan checks below are dependencies of the whole step. A flat store helper alone is insufficient. |
| Admit facts and decide a condition; pay for named terms and justified incremental updates | `kernel/assumptions.rs`, `kernel/equality_graph.rs`, `kernel/difference_graph.rs`, `kernel/assumptions/condition_reasoning/decision.rs` | `kernel/assumptions/condition_buckets.rs`: `equality_class_hits_and_anchored_misses_stay_indexed`, `interval_queries_do_not_walk_symbolic_order_components`; graph late-merge/fork controls | Source candidate F1: owned-anchor pointer distinctness still enumerates equality components/compositions. Coverage gap: total admission/propagation work across growing shared classes, beyond covered shapes. |
| Select, consume, fold or unfold ownership; pay for explicitly selected pieces/body | `ResourceContext::{satisfies_fact,without_fact_incrementally_impl,consume_unit_owned_memory}`, `ExecutionProofCore` fold construction | `kernel/loans/tests.rs`: `call_fragment_composition_stops_at_a_fixed_gap`; `kernel/proof/execution/tests.rs`: `constructing_an_instance_fold_pays_for_its_body_once`; source fold/unfold controls | R1 reachability gap for other quantities; R2 source candidates for ownership validity, alias/root discovery and overlap. |
| Observe separation or resource facts; pay for selected operands/evidence | `surface/proof/proof_object/splits_and_scopes.rs`, `kernel/proof/facts.rs`, `kernel/assumptions/memory_reasoning.rs` | source `observing_one_owner_ignores_unused_parameters`; transport footprint tests, including `two_footprints_do_not_expand_into_a_cartesian_product` | F2: composition/member bucket growth remains a coverage gap; frontier opening no longer reconstructs a composition-only context. |
| Check a write against loans; pay for selected conflict/evidence, not all loans or aliases | `LoanLedger::permits_memory_access_with_assumptions`, called by memory-access checking | `kernel/loans/tests.rs`: `write_barrier_does_not_enumerate_overlapping_loans`, `writes_without_active_memory_loans_do_not_walk_pointer_aliases` | L1: aliases with active loans and symbolic-loan comparisons. Zero-loan and concrete-overlap controls do not finish this operation. |
| Apply a modular call, transfer resources and finish it; pay for selected contract and effects | `kernel/functions.rs`: `execute_verified_function_applications_with_suspension`, `call_kept_ownership`; `kernel/proof/execution.rs` | source `a_call_ignores_unrelated_owned_objects`; `kernel/functions/stable_view_call_tests.rs`: `returning_one_borrowed_owner_does_not_rebuild_its_memory_block` | C1: residual instances, non-argument-direct composites, and number of resource families. E1: execution/publication/completion accounting. |
| Split/join branches and enter/exit loops; pay for explicit arms/interfaces and actual changes | `kernel/api.rs`: `abstract_c_state_for_interface_join_across`; `kernel/loops.rs`; `kernel/proof/execution.rs` | `kernel/loops/contract_exit_join_tests.rs`, `kernel/loops/frame_resource_tests.rs`; branch availability and interface-join controls | J1 coverage gap: fixed-delta joins across growing stable state; loop-head abstraction uses a different policy. Existing growth allowances do not establish ambient independence. |
| Apply an explicit equality, arithmetic or transport certificate; pay for written nodes/premises | `kernel/proof/{transport_certificate,integer_arithmetic,term_rewrite}.rs` | `kernel/proof/transport_certificate.rs`: history independence, explicit-node linearity, selected resource fields; `kernel/proof/integer_arithmetic/tests.rs`: repeated premise and shared-DAG controls | Coverage gap: map every Surface certificate driver through lowering, premise lookup, application and publication; preserve cold expansion/replay evidence. Do not re-enter discovery during application. |
| Introduce binders, apply logical rules and publish checked results; pay for explicit proof structure | `ProofObject::apply_intro`, `ProofFacts::freshen_integer_forall_body`, proof execution event recording | selected term-rewrite, fact-key and event-publication controls | Q1 deferred nested-quantifier work; E1 deferred/revalidation candidates. A helper's flat lookup says nothing about repeated whole-body copying. |

Test paths in the evidence column are relative to `src/scaling_tests/`.
The source-level control suite is
[`step_shape_scaling_tests.rs`](../src/scaling_tests/surface/tests/step_shape_scaling_tests.rs).
It holds repeated roles to a no-drift rule and varies ambient objects/facts;
it is valuable integration coverage, not an exhaustive list of statements,
contracts, or resource shapes.

## Remaining transport expansion inventory

This is a migration checklist for the legacy transport dispatcher, not a count
of distinct slow walks. There are five remaining work areas; each may need more
than one fixture. A spelling variation belongs to its existing row rather than
becoming a new roadmap item. Paths below are relative to `src/`.

| Area | Remaining route and source anchor | Completion criterion |
| --- | --- | --- |
| T1: residual scalar observations | `surface/proof/fixed_state_proofs/fact_transport.rs`: load-variable/origin bridges in `check_fixed_state_fact_transport_using_facts_inner`, plus `certified_fact_transport_reaches_through`. Computed scalar comparisons over selected reads, constants, arithmetic/bitwise operators and `to_integer` now have an ordinary preservation/rewrite expansion. Other read expressions, computed addresses, alternate cell spellings, and range-selected evidence still reach these routes. | Select each necessary equality and address guard in planning; emit explicit preservation/rewrite steps. Start with one reduced case, and identify a missing primitive before adding one. |
| T2: logical structure and quantifiers | `certified_fact_transport_reaches`: top-level conjunctions with non-scalar leaves, top-level disjunction, implications with non-comparison leaves or binders, and universal-body recursion; `check_fixed_state_fact_transport_using_facts_inner`: `frame_quantified_transport`. | Decompose into ordinary logical steps and the already supported leaf proofs. Handle logical forms beyond scalar conjunction selection/regrouping and matching propositional trees under implications with scalar comparison leaves; give non-scalar leaves, guards and binders their own replay/refusal fixtures. |
| T3: resource, range, and definedness facts | `certified_fact_transport_reaches`: separation/containment descriptor matching and atomic derivation of `CMemoryLoadable` / `CMemoryReadDefined`. | Replace each surviving route with named resource laws or explicit observations and guards. Do not count already converted current-snapshot viewability restrictions as outstanding. |
| T4: proof-context adapters | `surface/proof/proof_object/fixed_state_steps.rs`: `apply_transport_using`, `apply_pure_transport_using`, `apply_fixed_state_transport_using`, `apply_execution_transport_using`; post-execution handling in `surface/proof/driver/claims.rs`. | The same supported derivation expands at a focused execution goal, a pure/fixed-state proof, and a completed outcome. No adapter may retain an opaque transport simply because the proof phase differs. |
| T5: discovery and legacy dispatcher retirement | `plan_explicit_fact_transport`, transition/effect collection in `check_fixed_state_fact_transport_using_facts_inner`, and `surface/proof/proof_object/execution_statements/search.rs`'s bare transport planners. | Budgeted discovery emits ordinary steps, including selected footprint evidence. Remove search from the explicit-operation path and retire the legacy dispatcher once its supported cases have ordinary expansions or deliberate bounded refusals. |

T5 includes an explicit known cost violation: the legacy fixed-state route
rebuilds transition assumptions with `assume_proposition_uncharged`, and its
source comments acknowledge path-linear work. Converting a surface spelling
does not remove that shared implementation; the endpoint is to make it
unreachable from expanded proofs and then remove the obsolete route. Keep
source/result normalization and premise/effect collection in this review too.

For each row, retain a positive expansion/replay example with implicit solving
disabled, relevant refusal controls, and deterministic growth evidence. Finish
with a boundary test that expansion cannot create `ProofSearch`; the absence of
`transport` text in a few examples alone is not the global guarantee. This
inventory does not classify all non-transport entries in the operation ledger.

## Outstanding measurement ledger

### R1: remaining fragment-selection routes — reachability gap

In [`resource_algebra.rs`](../src/kernel/primitives/resource_algebra.rs),
`without_fact_incrementally_impl` enumerates/normalizes suppliers outside the
view and unit-owned routes; `satisfies_fact` has the corresponding other-quantity
route. Surface validation rejects quantities directly on memory. First identify
a supported producer and complete fold/transfer caller, or establish that the
route is unreachable and remove/classify it. If reachable, fix one requested
footprint and grow rejected suppliers; separately grow genuinely consumed
pieces. Test symbolic/wide carriers, gaps, ambiguity and persistent parents.

### R2: ownership validity and overlap — source candidates

`owned_validity_candidates` and incremental validity checking still have
symbolic-bound and multiple-coordinate-origin paths. Single-block count and
constant-coordinate neighbor shortcuts do not settle multi-block alias/root
discovery. `memory_ranges_proven_overlapping_with_separation` explicitly
constructs two alias lists and visits their product when constant coordinates
cannot settle the comparison.

Hold one inserted owner and one relevant neighbor fixed. Independently grow
same-block owners, owned blocks, coordinate origins and exact/offset aliases;
use symbolic bounds and different origins, not just the indexed constant case.
Measure the complete ownership addition/fold, including successful disjointness
and overlap refusal. Distinguish this from output-sized explicit composition.

### F1: pointer distinctness — source candidate

[`decision.rs`](../src/kernel/assumptions/condition_reasoning/decision.rs)'s
`pointers_distinct_by_owned_anchors`, reached from pointer equality decision,
builds both pointer equality components, compares them and visits listed
compositions/member pairs. Grow aliases and composition memberships while
holding the decided condition and two owners fixed. Include misses and repeated
queries through a simple checker; decide whether this route needs explicit
separation rather than discovery. Direct scalar equality tests do not cover it.

### F2: separation observation — remaining coverage

Frontier `have` opening no longer constructs a composition-only context or
admits the selected separation from it. Its explicit proof must establish that
fact. `have_opening_does_not_copy_ambient_compositions` grows unrelated owners
at 4/16/64 with a fixed selected goal and proof.

Other selected observation routes still need composition/member bucket growth
coverage and the owned-anchor discovery repair tracked under F1. Removing this
copy does not establish a bound for every separation observation.

### L1: write restrictions from active loans — source candidates

[`loans.rs`](../src/kernel/loans.rs)'s
`permits_memory_access_with_assumptions` constructs `memory_range_aliases` when
memory loans are active, then visits symbolic protected ranges in the query's
block and exact-alias blocks. The no-loan shortcut and concrete conflict-witness
index leave these routes intact.

Use an actual write with a fixed owner, expression and changed cell. Independently
grow aliases with one active loan, then same-block symbolic loans with a fixed
alias set. Include permission, refusal and optional diagnostic, cold/repeated
queries and branch retention. Cache protection is a separate operation; its
exact-origin retention index is not permission to write. Retain nested-loan,
width, overlap and ended-scope safety controls.

### C1: modular call framing — source candidate, also in scaling roadmap

When a verified call has memory effects,
[`functions.rs`](../src/kernel/functions.rs) calls `call_kept_ownership` on the
caller frame. It enumerates owned instances and composite families; bodies
without the argument-direct property are opened. Skipping members of one direct
family does not establish independence from the number of families.

Hold the callee contract/effect fixed and grow kept instances, non-direct
composites, then distinct direct families. Measure call preparation, execution
and completion together; include memory/condition/witness-dependent bodies and
refusals. Coordinate with [Scaling](scaling.md), cause 3, without duplicating its
implementation work or changing its priority here.

### M1: reads, caches and history — coverage gaps

The [memory-history roadmap](fact-aware-frame-walks.md) names read-side
`CellsForgotten` projections and bulk-write preparation. Inspect
`CMemory::prepare_store_cache`, its callers, and bounded cell-source queries
separately. A derivation edge named `CellsForgotten` does not itself establish
an unbounded history search: the inspected cell-source route counts real hops
against `max_hops` and gates its extended bridge.

Keep the read/store/explicit transport fixed while growing prior snapshots,
cached cells, compact runs and holes independently. Measure cold misses and
repeated adjacent/non-adjacent reads; grow genuinely overwritten pieces as a
separate output-sized control. Retain exact typed-read identity, initialization,
partial overwrite, freed-pointee and provenance refusals. New primitive designs
belong in the design/build discussion, not this audit pass.

### J1: branches and loops — coverage gap

`interface_abstraction_work_scales_with_unrelated_locals_and_memory` currently
allows up to 3x charged work when stable state doubles. It is a loose growth
check, not evidence that a fixed one-local change ignores ambient state.
`abstract_c_state_for_interface_join_across` already uses persistent differences
for parts of this operation; do not infer a scan just from the weak assertion.
The `JoinLocals::Stable` loop-head policy has different traversal behavior.

Measure the complete split/join and loop entry/exit at fixed arms, changed
locals and interface size, growing stable locals/cells/resources and prior
joins. Separately grow explicit arms, changed entries and invariant text.
Classify retained-state traversal against these actual inputs and changes;
exclude unavoidable explicit path enumeration from the ambient test.

### E1 and Q1: logical steps and evidence lifecycle — deferred evidence/gaps

[Scaling](scaling.md), cause 4, records repeated execution, result revalidation
and completion work. That description includes historical fixes and requires
caller-by-caller reconciliation before it is a current defect list. The completed preparation controls include
`prepared_call_obligations_execute_once_as_contract_and_context_grow`, named,
population/authority and return-fold construction, and the former failed/legacy
retry routes. All twelve selected controls passed at the reconciliation baseline.
Do not count these as still-unfixed repeated execution; they do not settle
condition/function theorem contexts, observation producers, or all joins and
final publication.
Count executor invocations and producer/result comparisons through complete
explicit steps, rewrites, joins and final publication, including uncharged
work. Reuse checked producer results rather than introducing another checker.

[Deep quantifier scaling](deep-quantifier-scaling.md) records repeated nested
`Integer` binder freshening. `freshen_integer_forall_body` still collects body
variables and substitutes when a binder collides; its non-collision shortcut
must be measured separately. Rebuild a complete nested-introduction curve with
and without ambient binder collisions. Old helper counts are historical, not
current complete-operation results. Preserve capture avoidance and expansion.
Both linked items retain their existing deferrals; the general constant-ish
checking claim must disclose them until resolved.

## Prevention coverage

`kernel::search::SearchPermission` gates ambient fact discovery, and
`build_support/search_boundary.rs` rejects selected forbidden calls and
iterator patterns. These guards cover named APIs/functions, not arbitrary
Rust iteration, allocation or structural comparison. `CheckingWorkScope`
attributes charged work inside selected helpers independently of enclosing
search. It does not establish coverage of every checker or detect uncharged
work. Operation closure therefore needs both a source-boundary argument and
complete-operation scaling controls; neither mechanism alone proves the rule.

## Next design/build cycle and completion

The behavior-preserving architectural split is described in
[Separate proof operations from proof search](../design/proof-operations-and-search.md).
Use its frozen dependency inventory to remove operation-to-search calls one
route at a time. Mixed callers now have semantic classifications; no strict search-free
execution guarantee is claimed. The measurements below feed that migration.

Choose one of these slices for the next design/build cycle; this audit does not
authorize a new primitive or a verifier behavior change.

| Candidate | First concrete step | What completing it would establish |
| --- | --- | --- |
| Boundary enforcement / interface cleanup | Extend the theorem-operation discovery guard to the next audited primitive, identifying existing exceptions before enforcing it. The inventoried search/support adapters have been extracted. | Clear ownership of discovery; guards must distinguish allowed driver solve from search inside primitives, even when invoked by solve. No claim to detect arbitrary loops. |
| Arithmetic obligation generation | Reduce one operator's inline safety decision; reproduce the spelling and position-drift controls above before designing a retained result plus obligation. | That operator generates and publishes bounded work while the driver alone solves its safety goal; no promise to migrate all arithmetic in one patch. |
| L1 active-loan write | Fix one write and owner, grow aliases with one active loan, then symbolic loans with fixed aliases. Write the complete-operation red scaling test first. | Evidence of a concrete remaining scan, or a closed coverage gap if flat. Choose an index or explicit-proof repair only after the result. |

F2 and C1 remain subsequent measurement candidates, followed by R2, R1
reachability, and J1/M1/lifecycle coverage. Declaration-validation search and
legacy transport T1–T5 remain separate design tracks; preparation completion did
not remove either. The inventoried operation/driver adapters have been extracted. This clears
that migration list; it does not remove the direct operation/search dependencies
or prove that all generated operations are fast.

For whichever slice is selected:

1. For each operation, retain source caller, input/delta definition, independent
   ambient axes, multi-size deterministic results, cold/repeated failures,
   semantic controls, and the checking/search boundary. Fix a complete route;
   do not mark the operation done because a common special case is flat.
2. Add source-level integration controls as well as helper tests. An expanded
   proof must replay without search. Attribute excessive checking to checking,
   even inside `solve`; `CheckingWorkScope` currently covers selected helpers,
   not every operation. Audit uncharged loops and deep comparisons as well as
   charged counters. No budget increase or warm cache substitutes for a bound.
3. Reconcile the adjacent roadmap items and fill the operation coverage gaps
   before claiming the general principle. Removing the named loops alone is
   insufficient. Keep this document an inventory of remaining evidence/work,
   not a history of completed PRs; move durable guarantees to the efficiency
   documentation and retain their tests when rows are resolved.

Persistent branches retain their parent contexts. Proof repairs preserve the
original C and contracts, using explicit separation and ordinary preservation/equality steps
at exact footprint entry/exit snapshots. Whole-region preservation must be
explicit composition, not a hidden transition walk. Inconclusive checking
cannot establish equality or preservation, and explicit proof application must
not reconstruct identities or search for intermediate states.

