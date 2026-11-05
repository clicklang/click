# Separate proof operations from proof search

Status: proposal for review; no implementation or semantic change.
Source baseline: `5303369f1`. This proposal restores the efficiency requirements
of the original [proof-object design](https://github.com/clicklang/click/blob/22eca252da95f6167d6a4dc7990b889c34355c2f/issues/proof-object-api.md),
using the existing proof state rather than creating a second representation.

## Design check

- **Parts:** proof-object operations, Surface tactic dispatch, persistent-state
  access, and search orchestration. Symbolic execution remains a proof operation.
- **Boundary:** `ProofObject` operations are fast; `ProofSearch` discovers which
  operations and explicit arguments to use. Search may call operations, never
  the reverse. State maintenance inherits the fast-operation bound.
- **Fast cost:** selected statement/rule/definition size and necessary delta,
  up to indexing factors. Candidate buckets and histories do not become explicit
  input merely because an index selects them. Each migrated operation needs
  fixed-input tests growing both unrelated state and related buckets/classes.
- **Slow result:** an ordinary successor with its successful explicit operations
  retained for expansion. Existing certificate primitives are used first. A
  missing expressible primitive requires a separate design discussion.
- **Lowering:** explicit operands remain fact-stable. Search selects evidence;
  it must not change how a written term lowers. No lowering changes are proposed
  in this documentation pass.
- **Refusal:** a fast operation returns a missing obligation or a rule-specific
  refusal. Search exhaustion identifies the attempted goal and how to provide
  explicit evidence. An operation-cost breach is a performance defect even
  while search is running.

## The contract

> An expanded proof can be executed without constructing or accessing a
> `ProofSearch`, and without entering a remaining legacy slow operation.

There are two independent obligations:

1. **Architecture:** search is unavailable during explicit execution.
2. **Complexity:** the operations that remain obey the fast bound, including
   state updates, lowering, premise lookup and publication.

Neither implies the other. A hidden loop inside an operation violates the
second even if no search object exists. A bounded search still belongs behind
`ProofSearch`, even if it happens to be quick on current examples.

Preserve one immutable proof state, one set of semantic rules and one retained
operation history. Search is not a second proof representation. There is no
conversion from a slow proof to a fast proof and no validation pass to rebuild
what successful operations already established.

## Interfaces

Retain `kernel::proof::ProofObject` as the authority for semantic successors.
Retain the current Surface `Proof` wrapper for source context and provenance;
its explicit-operation interface is the source-facing form of `ProofObject`.
Do not rename both types or collapse language presentation into the kernel.
Remove discovery methods from that explicit interface into `ProofSearch`.

Illustrative API, not a proposed new public Click syntax:

```rust,ignore
// Existing persistent semantic handle. Named methods remain preferable to
// an untyped escape hatch accepting arbitrary callbacks or mutable state.
impl ProofObject {
    fn focus(&self, goal: GoalId) -> Result<Self, Refusal>;
    fn apply_rule(&self, rule: ExplicitRule) -> Result<Self, Refusal>;
    fn advance(&self, statement: StatementId, evidence: ExplicitEvidence)
        -> Result<Advance, Refusal>;
}

enum Advance {
    Done(ProofObject),
    NeedsProof(PendingOperation),
}

// Source-facing session over the same persistent Proof/ProofObject.
struct ProofSearch<'session> { /* budget, capability, search-local state */ }
impl ProofSearch<'_> {
    fn solve(&mut self, proof: &Proof, goal: GoalId) -> Result<Proof, SearchMiss>;
    fn advance(&mut self, proof: &Proof, statement: StatementId)
        -> Result<Proof, SearchMiss>;
}
```

`ExplicitRule`/`ExplicitEvidence` stand for the existing typed rule inputs,
selected premises, resource identities and certificates, not a new universal
certificate format. Evidence supplied from source is applied by the existing
primitive operations. Opaque authority produced in this session is retained,
not re-derived by an additional checker.

`PendingOperation` is a proposed interface shape for the prepared execution
already handled by `finish_prepared_step`. It exposes the next obligation and
retains work already performed. It is private, tied to the exact persistent
root/frontier, and cannot publish the pending statement's effects before its
obligations are discharged. Discharge uses ordinary proof operations; resumption
must not rerun the statement for each obligation. Reject stale or wrong-branch
use by retained identity, not deep state comparison. Implement only the
continuation structure required by the first operation, not a general new IR.

Branching and scopes use the existing typed split/join operations. Failed search
branches discard persistent descendants without changing their parents. The
successful result retains precisely the operations expansion will serialize.

## State access is part of the interface

Separate access to persistent storage into two views, without copying storage:

| Operation view, available to `ProofObject` | Search view, requires a live `ProofSearch` capability |
| --- | --- |
| Exact fact membership; named premise lookup | Enumerate possible premises |
| Canonical equality/coordinate lookup with a documented bound | Enumerate aliases, walk candidate equality paths |
| Selected owner or a bounded singleton/conflict query | Enumerate possible owners or partitions |
| Exact snapshot/address read; one explicitly justified transition | Discover a path through memory history |
| Persistent updates proportional to a necessary delta | Try alternatives on persistent descendants |

A bounded query may return `Missing` or `Ambiguous`; it must not silently try a
longer route. Refusal does not authorize a write, equality or preservation.
Enumeration of explicitly supplied premises or actually consumed pieces is
allowed and charged to that explicit operation. Internal summary construction
needs an amortized argument across cold/repeated queries and persistent forks;
it cannot merely relocate the ambient scan into insertion or invalidation.

Keep raw collections private to their storage modules. Do not expose unrestricted
`Deref`, iterator-bearing context objects, or callbacks that can execute search
through the fast view. Initially audit and restrict the APIs used by the first
store slice; broader raw APIs remain named migration dependencies until audited.

## Module and capability arrangement

Use the existing single-crate layout initially:

- `kernel/proof/`: semantic proof operations and persistent proof state.
- `surface/proof/proof_object/`: explicit source operation drivers and provenance.
- `surface/planning/`: `ProofSearch`, strategies, implicit closing, omitted-argument
  discovery, and adapters to candidate enumeration.
- Persistent-state modules: bounded operation API and a distinct search view.
  Search-view implementations can reside beside private storage; they expose
  candidates, never semantic successor authority.
- Source tactic dispatcher: orchestration outside the fast API, choosing either
  an explicit operation or a `ProofSearch` request.

Dependency direction is search -> operations -> persistent state. Source dispatch
may reach both interfaces. The fast drivers and kernel operations may not import
or invoke planning, even through re-exports, traits, function pointers or callbacks.
Keep diagnostic-only sampling separately bounded; it is not a search capability.

Evolve the existing `SearchPermission`, rather than add a parallel token. Today
`surface/planning/permission.rs` lets planning helpers independently construct
it. Instead borrow it from a live, budgeted `ProofSearch` session; candidate
iterators borrow the session too and cannot escape it. Move the capability type
to a neutral boundary module so storage does not depend on Surface planning.
Its fields remain private; one session factory is the only authorized constructor.
Rust visibility protects fields and private views. Because sibling-module factory
restriction is not fully expressed by `pub(crate)`, the source-boundary guard must
pin that constructor and its exact callers. Do not claim crate-local visibility
alone establishes the dependency graph.

Extend `build_support/search_boundary.rs` and `tests/search_boundary.rs` to pin
fast modules, search entry points, capability issuance and each temporary exception.
Test forbidden imports, re-exports, trait adapters and indirect references.
The present scanner is not a full Rust call-graph proof; retain that limitation
explicitly. A future crate split is an option if module enforcement is insufficient,
not a prerequisite for this proposal.

## Explicit-only execution and expansion

Add one session policy for explicit execution. Unlike `without_implicit_auto`,
it disables all search, not just the implicit closer. Construction of a search
session and use of a pre-existing search capability both reject under that policy.
Search-view access checks the policy as well; a session created before a nested
explicit-only scope cannot bypass it. Use scoped restoration on errors/panics
and propagate the policy to any verification worker. Do not use a process-global
flag that interferes with other claims or concurrent tests.

The ordinary dispatcher preserves the convenience of bare `step()`: run the fast
operation; if it leaves an obligation and search is permitted, the dispatcher
asks `ProofSearch` to discharge it. This orchestration does not live inside the
fast operation. Explicit-only execution reports that obligation instead.
The same distinction applies to bare `fold`, omitted transport arguments, implicit
proof tails, and explicit smart tactics—not just a list of tactics named `solve`.

Full expansion serializes successful operations and arguments, then verifies the
result in a fresh explicit-only session with legacy slow operations disabled.
Partial expansion may leave search elsewhere and must not claim whole-proof
search freedom. Existing serialized-source replay remains an independent tool
check; search success does not replay its own just-constructed proof internally.

Initially the strict runner will expose unmigrated paths. Report those by their
exception IDs; do not make the global expansion guarantee until the relevant
expanded corpus passes. Already migrated slices get strict tests immediately.

## Initial boundary inventory

These entries are source-inspected at the baseline above. They are not fresh
red scaling measurements or an exhaustive count. The [operation audit](../roadmap/smart-tactics.md)
records remaining measurement shapes and semantic controls.

Two orchestration seams need separating; these are legitimate searches currently
reachable through the mixed Surface `Proof` API, not kernel soundness defects:

| ID | Current route | Proposed disposition |
| --- | --- | --- |
| D1 | `Proof::apply_step*` / statement drivers -> `apply_bare_statement_step` -> `prove_obligations_by_auto_or_name_the_first_missed` | Keep explicit application on `Proof`; move automatic obligation completion to dispatcher/`ProofSearch`, retaining prepared results. |
| D2 | `planning::disjunction_candidates` and `PropositionSearch` methods -> independent `SearchPermission::new()` calls | Require a session-borrowed capability at these entry points; do not allow helpers to start invisible search. |

Seven legacy traversal records need a fast-operation bound or removal. These
are candidate exception records, not seven fully classified bugs; splitting a
record into exact caller edges may increase the count without adding new scope.

| ID | Fast operation -> current traversal | Ambient growth / exit criterion |
| --- | --- | --- |
| L1 | Write loan restriction -> `LoanLedger::permits_memory_access_with_assumptions` -> `memory_range_aliases` | Alias class with an active loan. Select bounded evidence or move discovery to search; zero-loan shortcut is insufficient. |
| L2 | Same write restriction -> iteration of block-keyed `unindexed_memory` protected ranges | Symbolic loans with fixed write and aliases. Establish an efficient permission rule with explicit evidence where needed; cache-retention evidence cannot authorize writes. |
| L3 | `ResourceContext::try_compose_into_valid_context_with_occurrences` / validity helpers -> `owned_validity_candidates` | Owners, roots and aliases outside constant-coordinate shortcuts. Bound selection and updates, or expose a dischargeable obligation. |
| L4 | `pair_validity_error_with_separation` -> overlap helpers -> `memory_ranges_proven_overlapping_with_separation` -> nested alias loops | Product of the two classes when constant coordinates fail. Use bounded relation/evidence, not alternative-pair discovery. |
| L5 | `decide_pointer_disequality` -> `pointers_distinct_by_owned_anchors` -> equality components and composition/member pairs | Related aliases and compositions. Explicit separation or a bounded direct query must replace discovery. |
| L6 | `Proof::begin_have_spelled` -> `with_selected_composition_separation` -> `compositions_only` | All retained compositions copied into a fresh context. Preserve selected evidence without rebuilding an ambient context. |
| L7 | `execute_verified_function_applications_with_suspension` -> `call_kept_ownership` -> residual instances/composite families and non-direct bodies | Caller-kept resources and families with fixed callee effects. Retain/query frame authority without opening the ambient frame each call. |

For L1/L2, the scalar-store route is
`eval/statements.rs::stable_loan_memory_range_outcome` ->
`CState::stable_loan_memory_access_refusal` -> `LoanLedger::memory_access_refusal`
-> `permits_memory_access_with_assumptions`. Calls, loop havoc and population
operations also reach the barrier and need separate caller records. L3/L4 live
in `kernel/primitives/resource_algebra.rs`, L5 in condition reasoning, L6 crosses
the Surface scope driver and kernel fact store, and L7 lives in `kernel/functions.rs`.

Do not invent seven entries in a generic runtime allowlist yet. The first build
stage must enumerate each actual caller and choose the narrow adapter boundary.
Use records of `(ID, caller module/function, callee, growth axis, strict test,
removal condition)`; reject missing, stale or additional callers in the build
check. New dependencies cannot silently enter an existing broad record.

A temporary legacy adapter is an explicitly acknowledged fast-boundary violation,
not another valid fast API and not a `ProofSearch` constructor. It preserves the
old behavior only in compatibility execution, charges/report its ID, and refuses
in strict execution. Some loops are inline and some are global restrictions:
merely wrapping them does not provide an expandable proof. Migrate them to a
bounded operation or a real search-plus-explicit-proof route before deleting
the exception. Never replace their refusal with permission.

Unclassified dependencies remain a separate list, not hidden behind a claim
that there are only seven problems:

- Other-quantity fragment selection: establish a reachable source producer.
- Read-side cache projections and bulk writes: distinguish bounded transitions
  from history discovery and necessary changed cells from ambient candidates.
- Branch/loop abstractions and fact/index maintenance: establish delta bounds,
  including repeated branches and growing related graph classes.
- Rule lowering, evidence publication/completion and nested binder freshening:
  reconcile deferred work and account for copying/comparison outside search.
- Remaining simple tactics and indirect helper calls: complete the entry-point
  classification beyond this initial list. Inspect code, not just imports.

## First complete slice: a store

Hold the source statement, access width and changed bytes fixed. Trace the full
path through source lowering, pointer evaluation, bounds/initialization/provenance,
owner selection, loan restrictions, memory/cache update, and proof publication.
Each stage names its bounded query or explicit evidence and its state delta.
Existing retained typed reads, separation facts, `.footprint` and transport
certificates are the starting vocabulary. Do not invent an effect object or a
new certificate language as part of the interface refactor.

L1 and L2 are the first measurements, not preselected implementation solutions.
Grow aliases with one active loan, then symbolic loans with fixed aliases; measure
successful and refused writes, cold and repeated queries, and persistent siblings.
Also grow unrelated owners, cached cells and prior snapshots through the complete
store. Separately grow genuinely changed ranges. Discuss any missing explicit
rule before changing permission or preservation semantics.

Acceptance for this slice: the complete explicit store invokes neither search
nor a legacy adapter; its deterministic curves obey the bound; an automatically
found proof expands and cold-replays through that same route; aliasing, overlapping
loans, ended scopes, widths, initialization, lifetimes and provenance retain their
intended refusals. The original C and claims remain unchanged.

## Migration stages and review points

1. **Approve the interfaces and inventory.** This document is that proposal.
   No behavior change, counters or exception wrappers land with it.
2. **Build the boundary without changing proof rules.** Introduce the search
   session, move orchestration, restrict capability issuance, inventory exact
   legacy callers, and add strict execution. Negative tests attempt capability
   construction/use, hidden dispatch and legacy access from explicit execution.
   Run existing proofs in compatibility mode and migrated controls in strict mode.
3. **Design then build the store slice.** First obtain complete-operation red
   curves and agree on each missing primitive. Remove its exact exception edges;
   do not broaden an allowlist or substitute a different hidden scan.
4. **Migrate by complete operation.** Follow the operation audit. Report exact
   exception edges, unclassified entry points and strict corpus coverage together;
   a shrinking exception count alone is not proof of completion.
5. **Remove compatibility access.** All supported explicit operations are
   classified, legacy edges are gone, ordinary expansion replays strictly, and
   scaling controls cover maintenance as well as queries. Preserve any explicitly
   deferred work as a disclosed limitation; do not claim the global contract
   while it remains a violation.

Review decisions proposed here: retain the existing proof representation; use
`ProofSearch` for session-owned discovery; require strict execution to reject both
search and legacy access; start with a complete store. The exact store evidence
interface and any new primitive remain a later design decision backed by a red
measurement.
