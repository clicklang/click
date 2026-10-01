# P1: Authority migration

## Goal and dependency order

Replace implicit counted-population access with explicit population authority.
Keep `count(...)` as an observation, make resource types consistent regardless
of proof fields, and remove `guarded_by`. Use ordinary resource composition and
`owns`/`views`/`consumes`/`produces` to connect population accounting to memory
and mutex operations. Do this migration before extending the
[concurrency demo](concurrency-demo.md) to exact shared-worker accounting.

This is the selected direction, not implemented syntax or a claim that current
sequential proofs are unsound. It supersedes the whole-population mutex-custody
extension plan in the [counted counter investigation](../design/concurrency-probes/shared-count-authority.md).
The older [fractional sum proposal](../design/concurrency-probes/explicit-authority.md)
is background, not authorization to introduce its entire interface.

## Problem and invariant to establish

A closed resource that asserts a relationship between memory and a population
must control changes to both sides. No thread may create or consume members
behind that resource's back, leaving its count-dependent invariant false.
Checking only whether a `count` expression has authority is insufficient:
population transitions must preserve that authority's invariant as well.

Today the implementation mixes independent concerns:

- Surface countability is selected by the absence of proof `field` declarations
  (`ResourceDefinition::is_countable` in `src/surface.rs`).
- Count expressions in body facts select special counted-population handling
  during resource lowering in `src/surface/verification.rs`.
- One positive owned unit can open a shared population body in sequential
  proofs. Open-scope checks and thread confinement prevent concurrent use of
  that rule; this is not a general shared-resource authority mechanism.
- Local mutex custody hides body permission in retained units while unlocked
  and demands complete population accounting at publication and release.
  The held/unheld helper tests pass, but worker transfer remains unsupported.

Do not extend these special cases as the foundation of concurrent refcounting.
Preserve their useful tests while replacing the permission model.

## Intended resource model

`resource reference(p: ...)` declares a family. `reference(p)` describes that
family with fixed parameters, whether or not the declaration has proof fields.
An owned instance owns its declared contents. Coexisting instances must have
compatible ownership: two ordinary instances cannot independently own the same
exclusive C field. Distinct, disjoint objects may have instances of the same
family. Proof fields record per-instance state; they do not select whether a
family has a population or can be counted.

Count tracks occurrences/units in a selected population, including individually
identified field-bearing members. Equal parameters do not erase instance
identity or merge different field values. This does not require immediately
supporting symbolic quantities of field-bearing instances: preserve identity
and distinguish a quantity-syntax limitation from inability to count a family.

A member no longer exposes shared population memory merely because it is one
of several units. Private contents may be opened using ordinary ownership;
access to shared accounting state comes from the resource that owns it.

### Proposed authority interface

Use the following as the design target, not parser-ready implemented code:

```text
resource reference(p: struct object*) {
}

resource control(p: struct object*) {
    owns p->refs;
    owns authority(reference(p));
    fact p->refs == count(reference(p));
}
```

`authority(reference(p))` is a proposed built-in resource, exclusively held for
one population identity. It controls checked population changes; it does not
own all distributed references or grant arbitrary access to their contents.
The surrounding ordinary resource owns the actual C counter and states the
invariant. Authority itself does not require a mutex.

Required semantics:

| Operation | Requirement |
| --- | --- |
| Observe a current `count(R(...))` | Matching population authority, exposed directly or through a checked resource invariant/contract boundary |
| Create or consume tracked members | Matching authority and checked population transition; consumption also supplies the owned members |
| Transfer existing members between owners | Ordinary ownership transfer; no count change |
| Split/combine quantities of interchangeable owned units | Ordinary quantity rules; no count change |
| Open a member's private contents | Ordinary access rules; this does not expose the authority's shared invariant |
| Close a control resource | Restore its contents and prove its facts at the updated population state |

Keep current observations distinct from historical snapshots. Copying a fact
about an earlier count does not authorize a fresh current count observation.
Opening a mutex-protected control resource must use fresh observations after
possible interference. At contract boundaries, a checked invariant may expose
its stated relationship without handing out duplicate authority; spelling a
count must never manufacture ownership or permission to update it.

### Decisions to settle before implementation

Specify these rules together, with a small kernel interpretation and source
examples. Review additional surface syntax before implementing it.

1. **Population establishment and retirement.** Establish an initially empty
   population only in the environment that actually creates its anchor's C
   storage. Receiving memory or an allocation contract claim grants no such
   permission. Establish each scope at most once per storage lifetime; retain
   that restriction after retirement. Pass authority explicitly to helpers.
   Retirement requires zero members; freeing the anchor requires all live
   authorities to be retired. Folding a wrapper cannot invent creation
   evidence. Implement C creation-event and invocation transport before
   exposing establishment to source proofs. Use `fold(authority(...))` for
   establishment and `unfold(authority(...))` for empty retirement. The existing
   `construct` is not authorization, and allocation custody is no longer the
   proposed bridge.
2. **Scope and patterns.** Support the exact populations used by refcount and
   the per-pool wildcard observation `count(pool_object(pool, _))`. Initially
   use disjoint governing scopes, not overlapping independent authorities.
   Specify how exact observations and member transitions resolve to a wildcard
   owner, including proved pointer aliases and transfer between two pools.
3. **Tracked versus ordinary resources.** Require authority for current count
   observations. Do not add authority obligations to unrelated ordinary
   resources. Once enrolled, members remain governed across opaque calls,
   wrappers, and worker transfer even if the callee never mentions `count`.
   Adding a declaration elsewhere must not silently change a family's semantics.
4. **Transition checking.** State what `produces`, `consumes`, local fold/unfold,
   and returns mean for tracked members. Preserve compatibility with ownership
   held elsewhere, without enumerating that ownership. A reference cannot be
   spent twice; restoring an `owns` input cannot hide a net population change.
   Distinguish relinquishing proof knowledge from a checked count decrement.
5. **Fact dependencies.** Define authority requirements for body facts,
   predicates, function contracts, snapshots, and loop invariants. An ordinary
   predicate containing `count` cannot bypass them. Authority borrowed through
   a call must be recovered with its updated state, not stale entry facts.

The new model requires explicit authority for tracked populations. Do not
invent an implicit sequential-authority fallback within it. The staged rollout
below temporarily retains the unchanged old model for unmigrated clients. Keep
`count`, ordinary resource binders, and named call maps; do not revive `<>`
resource templates, add a general algebra-definition language, or introduce
separate sum-specific built-ins in this migration.

The semantic reference is Iris's
[authoritative construction](https://plv.mpi-sws.org/coqdoc/iris/iris.algebra.auth.html)
and [frame-preserving updates](https://plv.mpi-sws.org/coqdoc/iris/iris.algebra.updates.html).
For every admitted transition, justify compatibility with any outstanding
ownership not supplied to the operation. A basic additive authority normally
bounds fragments; it does not automatically establish an exact population
count. State the extra accounting that justifies exact totals and final zero.
No claim of an Iris embedding or inherited soundness follows from similar names.

## Remove guarded_by

Remove `guarded_by` from declarations, parser/lowering, kernel metadata, and
active documentation once its checked associations are supplied by ordinary
initialization and resource transfer. Migrate examples and negative tests;
do not merely disable address validation.

Initialization deposits an actual owned control resource in a mutex. Locking
returns that resource and the acquisition guard; unlocking requires them back
with the invariant restored. Preserve authenticated protected-resource types,
initialization identities, lifetime checks, and stale/wrong-mutex rejection.
A control resource must also be usable sequentially with no mutex annotation.
Retain existing `mutex_live`, `mutex_use`, and `mutex_guard` behavior except
where integrating ordinary authority ownership requires a justified change.

## Staged rollout: build, migrate, then remove

Build authority support additively before changing existing examples or the
public default. The checkpoints below are ordered dependencies, not one large
patch. Each may take several coherent commits, but must meet its exit gate
before the next checkpoint starts. Keep the original C and properties fixed.

Checkpoint 0 has a [consumer inventory](../docs/internals/authority-migration-inventory.md)
and an approved [object-anchored lifetime protocol](../docs/internals/authority-establishment-review.md).
The first additive kernel slice checks exact unary population ownership,
creation-site restriction, once-per-lifetime establishment, transfer, and empty
retirement. A C event ledger checks heap and automatic-object
creation provenance, call-environment transport, and per-family history that
prevents late establishment after members were transferred away. Project-level
mode selection and `authority(R(p))` parsing/lowering are additive. A restricted
source bridge checks `fold(authority(R(p)))` for empty establishment and
`unfold(authority(R(p)))` for zero-count retirement against actual C creation
events. A partial checkpoint 2 checks one member's `fold(R(p))`/`unfold(R(p))`
as birth/consumption paired with its owned resource exchange. Members may have
a field-free body of private, concrete, owned C memory; opening such a member
exposes that body without changing its count. Current exact `count(R(p))`
observes the authority ledger. The transitions have independent certificate
checks. Verified ordinary C helpers can borrow and return the same exact
authority and member; standalone helper proofs treat their declared input as
an opaque population with no count or creator permission. Such a helper can
open a transferred member's private memory body, use it, and close it before
return. A verified helper can also create or consume one exact member with a
private owned-memory body while returning authority. Its contract transfers
the entire body through ordinary memory `consumes` or `produces` clauses, its
standalone proof checks the birth or death, and the call applies that change
to the concrete ledger. Creation checks live anchor storage. Checkpoints 1–5 now support the sequential
refcount group, current and historical exact count, checked authority-bearing
wrappers, private member bodies, numeric nested helper transfers, conditional
release, standalone symbolic batches, and shared-parent ownership through
named wrappers and nested helpers. Symbolic nested transfers,
field-bearing/wildcard populations, and worker/mutex migration remain pending
in checkpoints 6–12. `construct(...)` has not been
extended; authority establishment and empty cleanup use `fold`/`unfold`.
Update this status and the inventory as commits land.

| Checkpoints | Deliverable | What happens to old clients |
| --- | --- | --- |
| 0 | Baseline inventory and settled permission rules | Unchanged |
| 1–3 | Kernel support, checked updates, and usable source interface | Unchanged; new focused fixtures exercise authority |
| 4–7 | Sequential refcount, parents, field-bearing members, and pool | Migrate one dependency group at a time |
| 8–10 | Mutex integration, shared refcount, contribution/join accounting | Migrate remaining groups after their prerequisites pass |
| 11 | New semantics become the sole execution path | No unmigrated clients remain |
| 12 | Delete legacy code and `guarded_by` | Already verified without legacy execution |

### Rollout safeguards

- Keep the full existing corpus green at every landed checkpoint. No mass
  expected-failure changes, quarantine, weakened postconditions, or discarded
  negative tests to make a migration pass.
- Keep the legacy path temporarily for **unmigrated** verification units. A new
  authority proof must never retry through legacy rules when checking fails.
  This is implementation coexistence, not implicit authority in the new model.
- Select the temporary implementation path at an explicit verification-unit or
  project boundary, recorded in migration/test metadata and proof provenance.
  All reachable contracts, imported summaries, caches, and certificates must
  agree on the semantics. Reject mixed unchecked boundaries. Do not select the
  model from the presence of fields, discovery of a `count` expression, or
  whether a proof happens to succeed. Settle this boundary in checkpoint 0;
  do not add a permanent public `legacy` keyword.
- Maintain a migration inventory here or in a linked checked-in table. Record
  each affected project/fixture group, selected path, original property, and
  replacement regression. A group leaves legacy only when every dependency
  and its positive/negative proofs are ready.
- Run focused tests and the full `scripts/check.sh` before merging executable
  changes. Verify affected proofs before profile/expand/reverify/audit. Apply
  the repository's documentation gate to prose-only checkpoints. Rebase and
  rerun affected checks when the integration base moves.
- If a checkpoint fails, keep the incomplete work isolated. Retain the previous
  green checkpoint; never weaken the permission rule or mix old and new
  certificates as a fallback. Build scaling tests alongside new representations.

### 0. Inventory and freeze the migration contract (documentation/tests)

**Work:** Inventory `count`, quantity syntax, proof-field count refusals,
count-dependent bodies/predicates, abstract worker populations, and `guarded_by`
across examples, mdtests, design probes, kernel tests, and source-backed docs.
Group consumers by project/call dependencies. Record the existing pass/fail
properties, including tests whose current field-based rejection must become a
positive with explicit authority.

Resolve the decisions above into concrete allocation, observation, transition,
and retirement rules. In particular, fix fresh-population establishment and
exact-count meaning, and choose the temporary isolation boundary. Specify
wildcard scope semantics now; implementation may wait for checkpoint 6.
Identify any additional source syntax requiring user review before coding it.

**Exit gate:** A reviewer can tell which operations require authority and why,
how an authority is first obtained, and how new proofs cannot enter old rules.
Baseline gates pass. No existing resource semantics change.

### 1. Add kernel authority ownership (no existing client migration)

**Work:** Add population identities, exclusive authority ownership, tracked
membership, indexed scope lookup, and ownership transport. Supply checked
fresh allocation and retirement. Add exact-population observations for kernel
clients; authority allocation must not arise from ordinary folding. Keep the
new representation inaccessible to legacy rules and maintain separate proof
provenance/cache identities as needed.

**Tests:** Duplicate authority, wrong population, aliases, pointer reuse,
retirement with outstanding members, quantity regrouping, transfer without
authority, and independence from unrelated resources. Deterministic scaling
covers allocation, lookup, and transfer.

**Exit gate:** Kernel ownership and observation tests pass; existing source
examples still use their unchanged implementation path. Do not remove
`is_countable`, the old population representation, or `guarded_by` yet.

### 2. Add checked population transitions and fact dependencies

**Work:** Implement creation/consumption with the appropriate authority and
owned members. Define the exact-total conservation evidence. Connect updates
to checked resource exchanges, function entry/return, scoped restoration, and
current versus historical observations. Establish how private member contents
can be unfolded/refolded without deleting and recreating membership. Ordinary
ownership of shared C memory remains with the control resource.

**Tests:** Missing authority, missing consumed unit, double consumption, stale
count reuse, a closed control invariant surviving an unauthorized update, and
forged certificates. Include opaque-call and snapshot bypass attempts, not only
successful tactic execution. Test fact invalidation and update scaling.

**Exit gate:** The kernel independently checks both observation and transition
permissions. No source-level authority feature is enabled with unchecked
updates or a legacy fallback. Existing examples remain untouched and green.

### 3. Wire the source interface end to end on new focused fixtures

**Current slice:** A field-free ordinary control resource with owned counter
memory, one contained exact authority, and a count fact can be folded, opened,
closed, and unfolded. Checked rewrites validate the resource exchange and fact
against the current ledger total. A three-function fixture creates the control,
passes it through ordinary retaining and releasing helper contracts, observes
the returned count, and retires the empty authority before freeing storage.
The exact symbolic count at a helper entry is imported only through this
checked wrapper. Verification, selective expansion/re-verification, and audit
pass on this fixture. Other body shapes and migration of the existing
sequential refcount project remain outstanding.

**Work:** Parse/lower `authority(R(...))` through ordinary ownership clauses,
resource composition, named binders, and call maps. Wire the approved
establishment/retirement interface. Implement authority-dependent `count` in
facts, predicates, contracts, snapshots, and simple loop invariants. In the
new path, resource fields must not select population semantics. Initially use
exact populations and small members; broader cases have explicit later gates.

**Tests:** New tiny positive and negative fixtures for initialization, retain,
release, current count, zero, and a control resource opened/restored through
ordinary helper contracts. Add a test that new-mode proofs/certificates cannot
obtain legacy population-body permission.

**Exit gate:** A complete new proof passes verify, expand/reverify, and audit
using authority throughout. Diagnostics name missing source resources/facts.
The whole old corpus remains green. This is the first usable authority support;
only now start migrating existing clients.

### 4. Migrate the sequential refcount project

**Work:** First prove the same frozen C with an authority-based sidecar while
the old project remains the baseline. Then replace its sidecars and migrate
its fixture group in one green checkpoint. Cover
[the complete refcount example](../examples/refcount/README.md): initialize,
retain, symbolic retain/release, nonfinal release, final free, allocation
failure, and callers. Control owns the counter, authority, and appropriate
allocation/lifetime obligations; references are separate members.

**Exit gate:** All original claims hold on the new path, including exact totals
and final reclamation. The negative variants fail for the relevant missing
permission or false equality. This group has no legacy dependency; unrelated
examples have not changed semantics.

**Current frontier:** The canonical sidecar in `examples/refcount/` selects
authority semantics and verifies all seven frozen C functions, including
symbolic `amount` retain/release and the complete allocation-failure and
final-free pipeline. Its ordinary `control(obj)` owns the allocation, counter
memory, authority, and count equation. Checked symbolic batches cross helper
contracts and are consumed before final authority retirement. Focused
authority-mode negatives reject an omitted `free`, resource duplication,
double spend, and count observations without the matching live authority.

Four related positive fixtures now use authority: population/body equality,
initialization/finalization, independent populations, and retain/nonfinal
release. They preserve their original count claims and frozen C. Retain can
produce one member while holding an existing member; release can consume one
from a numeric quantity greater than one. Numeric imports remain bounded to
one net unit change; symbolic batches use their separate checked exchange.

Contract count observations require both current owned custody and checked
ledger custody. A folded control supplies the first only through its checked
resource definition, for the exact contained `authority(R(p))`; an entry-time
registration or a historical fact alone is insufficient. Its arbitrary entry
total comes from the authenticated control invariant and retains the checked
member-update delta. Transfer, consumption, and retirement immediately remove
the former holder's observation permission. Source proof execution and
certificate validation run the same rule. Regressions cover wrong populations,
absent ownership, views, nested calls, retirement, and historical versus current
observations. A false-zero regression ensures that authenticating an external
control does not assume its entry count is zero.

The ordinary abstract transfer fixture and missing-private-body negative now
use authority. Ordinary wrappers package and expose existing members without
changing their population; the kernel checks and retains those exchanges,
including proof operations after the C return.

Conditional release helpers use existing `consumes` and guarded `produces`
clauses to return control only on the nonfinal branch. Nested numeric calls
transfer authority and members explicitly, preserve updated population state,
and reject stranded ownership. Their postconditions observe the checked member
delta before the caller resumes. Symbolic nested transfers remain explicitly
unsupported; standalone symbolic batch proofs remain supported.

The sequential refcount group is complete: both
`counted_release_preserves_nonfinal_allocation.md` and
`population_initialized_cleanup.md` now use authority with unchanged C and
all original postconditions. Consuming authority requires proof that the exact
population is empty; this preserves a read-only `count(R(p)) == 0`, including
after free. It grants no membership-update, storage-access, or reestablishment
permission. An unrelated freed pointer cannot supply that evidence, and a new
object lifetime cannot reuse it. Imported authority cleanup independently
checks the global total, rather than merely local member exhaustion.

A generic authority-bearing storage resource can describe an object before its
C counter is initialized. Its helper-entry count is an arbitrary opaque value;
a declared counter equality is used only when the wrapper actually provides
one. Initialization can require zero and produce the first reference using
ordinary contracts. Checked wrapper opening supplies authority for helper
preconditions and historical count postconditions without changing actual
custody. Both migrated fixtures pass verification and expansion audit;
`authority_count_after_cleanup.md` covers zero before and after free, while
spent-authority and unregistered-family negatives preserve permission checks.

### 5. Migrate shared-parent ownership

**Work:** Move references through ordinary parent wrappers and nested helpers.
Migrate [both parent destruction orders](../mdtests/shared_heap_population_lifecycles.md)
and their related alias, allocation-failure, and final-release fixtures.
Preserve reads through the surviving parent and exact final reclamation.

**Exit gate:** Wrapped members retain their population identity, opaque calls
cannot change them without authority, and both frozen caller paths verify and
audit. Refcount and all unmigrated consumers remain green.

**Complete:** Both frozen destruction orders, surviving-parent reads,
allocation failures, and final reclamation verify under authority semantics.
The main sidecar audits all 48 smart sites; the related migrated fixture group
and all remaining consumers pass the full repository gate. The C is unchanged.
The migration also preserves checked early-consumption evidence at legacy
proof endpoints, so a nested extra consumption cannot be hidden at return.

The straight two-parent decrement-only helper uses borrowed control and a
borrowed surviving member plus one consumed member. Its existing inputs still
supply two units, and its output preserves the surviving unit's identity and
returns control unconditionally. This is a stronger natural contract for C
that cannot take a final-release branch. The earlier explicit
`consumes 2`/`produces 1` member shape and weaker conditional control return
using `old(count(child_ref(p->kid)))` remain unsupported at their modular and
deferred-certification boundaries. Checkpoint 5 does not claim those interface
gaps resolved; genuine conditional/free behavior remains covered by the main
shared-parent and branch fixtures.

### 6. Build wildcard and field-bearing member support before pool migration

**First capability:** Concrete creation environments support field-free
`authority(R(anchor, _, ...))`, with every trailing argument wildcard.
Dedicated `authority_wildcard_*` fixtures check local member creation and
consumption, aggregate totals, duplicate authority, wrong-pool updates,
nonempty retirement, and consumption of an unowned member. Kernel scaling
covers lookup and exchange beside unrelated pools. This is one independently
tested capability. Ordinary helper contracts now borrow and return wildcard
authority together with one concrete member, including nested calls. Their
entry total is arbitrary and preserves members retained by the caller; helper
entry grants no creation permission. Dedicated fixtures and kernel checks
cover custody, exact member identity, unchanged total, intended refusals, and
indexed transfer beside unrelated imports. Authority-only helper inputs now
support one field-free concrete member birth using ordinary `produces`, including
nested helpers. The checked update requires a count overflow bound, records the
actual created member, and independently checks the promised output identity.
Caller regressions retain two members while receiving the third. Helpers also
consume their one exact entry member using ordinary `consumes` and `unfold`,
including nested calls. Their arbitrary total falls by one while caller-retained
members remain owned. Return certification requires the actual checked decrement,
and regressions reject missing consumption, wrong identity or pool, missing
authority, and reuse after the call.
Private memory bodies also support nested opens and member-only helpers: two
slots can own disjoint cells in one allocation, and changing one preserves
the other's value and the population total. Opening and closing require the
member, not authority; creation and consumption still require authority.
Regressions reject missing member or body ownership, overlapping bodies, and
member-only count observations. Identified proof fields, exact subsets, and
bounded-pool migration remain separate subsequent changes.

Direct and nested consumption helpers now also return a memory-only member's
private body through ordinary `produces`. Caller regressions retain another
member, prove the decremented total, read both ranges, and reclaim the allocation.
Negative regressions reject missing authority, wrong-member consumption,
opening without consuming, and reuse of consumed membership or freed memory.
This adds no syntax and does not extend member facts or proof fields.

The inverse memory-only creation also verifies through direct and nested
helpers using ordinary `consumes` memory and `produces` member clauses. Caller
regressions retain another member, prove the incremented total, open both
bodies, and reclaim the allocation. Rejections cover missing memory or
authority, duplicate membership or independent body ownership, and a missing
count overflow bound. This capability needed only fixtures and documentation;
the existing checked member exchange and call transfer already support it.

Direct and nested helpers now move one unit memory-bearing member between
two wildcard authorities using ordinary `consumes` and `produces`. Per-pool
entry imports preserve arbitrary totals, and return checks both exact ledger
changes. Callers retain members in both pools, preserve private memory, and
retire both populations after cleanup. This remains a narrow same-family,
same-trailing-arguments transfer, not arbitrary multi-update support.

Unit members with private owned-memory bodies now also carry ordinary `fact`
invariants. Fold checks current facts; open exposes them and close requires
restoration; exact consumption exposes the invariant with its memory. Member
invariants can read only their own body, not unrelated ambient ownership.
Dedicated fixtures and kernel forgery regressions cover this independently.
Named proof fields and field-bearing population identity remain deferred.

Unit private bodies now also compose ordinary owned declared resources.
Direct and nested helpers transfer exact children into and out of members;
member-only nested opens expose their memory without authority. The child
population total is preserved, while the outer population records its birth
or consumption. Caller custody tracks the explicit contained-resource
frontier. Dedicated negative fixtures reject missing, mismatched, and duplicated
children, and kernel checks reject forged body exchanges. Built-in object
ownership is covered separately. Named proof fields remain a later increment.

Exact member counts under wildcard authority now have dedicated fixtures for
creation/consumption helpers, retained neighbors, and equal-member multiplicity.
Exact helper entry counts remain arbitrary and distinct from the family total.
The initial implementation admits concrete pointer/int32 indices and the
helper's selected member; unresolved aliases, partial patterns, and symbolic
batch subset observations remain deferred. Indexed lookup/update scaling and
rejections for missing authority and unproved exact cardinality are covered.

**Work:** Implement disjoint per-pool scopes, exact observations governed by a
wildcard authority, and extend the checked transfer beyond the memory-only unit case as needed. Count
individually identified members without erasing fields or treating equal
parameters as interchangeable instances. Add the private-slot example below.

**Tests:** Overlapping authorities, wrong-pool updates, aliasing, cross-pool
transfer, two disjoint field-bearing instances, exclusive-memory conflicts,
and private field changes that preserve membership. Wildcard queries/updates
need indexed, output-sensitive scaling coverage.

**Exit gate:** Small dedicated fixtures establish these capabilities before any
bounded-pool sidecar depends on them. The legacy field-based restriction still
exists only for remaining old clients; do not globally flip it yet.

### 7. Migrate bounded pool and remaining sequential count consumers

**Work:** Migrate [bounded pool](../examples/bounded-pool/README.md), preserving
checkout/return, resize, zero capacity, wildcard totals, private object writes,
and source-to-destination transfer. Move the pool invariant and population
authorities into its control ownership. Then migrate the remaining sequential
count/predicate/loop fixtures from the inventory in small dependency groups.

**Exit gate:** Original pool C and all claims verify with explicit authority.
Private object writes need no pool authority when they do not change the pool
invariant. No sequential consumer remains unaccounted for in the inventory;
concurrent and local-mutex legacy groups are listed explicitly.

### 8. Integrate authority with existing mutex transfers

**Work:** Allow an ordinary mutex-protected control resource to contain authority.
Verify concrete lock/unlock and independently checked acquiring/releasing
helpers, including fresh count observations, replacement state, and lifetime
holds. First add authority-based counterparts to the held/unheld population
helper and local-conservation fixtures, then switch those groups over.

Migrate `guarded_by` examples to initialization-established associations in
small groups. Preserve wrong-mutex, stale-initialization, and missing-state
negative coverage. Keep the old parser/metadata until the final removal gate.

**Exit gate:** Lock gives control ownership, unlock requires its restored
invariant, and a member alone cannot expose it. Neither the new proofs nor
helper certificates use special counted-population mutex custody. Parity,
ordinary mutex helpers, and all previous migrations stay green.

### 9. Add shared-refcount concurrency support and its acceptance example

**Work:** First test authority/member lifetime dependencies across create,
worker contracts, and join without admitting premature observations. Then
freeze and verify a small ordinary C program with two users, a retained owner
reference, locked retain/release, and final reclamation after users finish.
Handle creation failure and both completion/join orders.

**Exit gate:** References keep the object and mutex alive before acquisition;
updates cannot invalidate references held elsewhere; reclamation occurs once
only after the necessary references and use loans are recovered. Verify,
expand/reverify, and audit pass without a refcount-specific mutex rule. This
is a mutex-protected example, not an atomic-refcount or lock-free claim.

### 10. Migrate contribution and abstract worker-accounting fixtures

**Work:** Migrate [sequential exact two](../mdtests/counted_resource_contribution_counter.md)
and local contribution consumption, retaining scope-close and return
single-consumption checks. Separately migrate abstract worker-ticket/join
fixtures. A worker transition must possess authority or use a specifically
justified deferred transfer; join cannot retroactively authorize consumption.

Existing no-lock workers may expose a real expressibility gap under the new
rules. Resolve the protocol/contract design before migrating that group; do
not rewrite their C, drop their exact claims, or retain a hidden authority
bypass. Preserve create failures, either join order, and early/stale count
refusals. The shared-worker counter's final exact-two proof remains the next
concurrency-demo task after migration, rather than an extra completion gate here.

**Exit gate:** Every count consumer in the inventory has a checked new-model
replacement, including worker accounting. No legacy-only fixture is quietly
skipped or weakened. All new groups pass the full gate together.

### 11. Switch the default only when the migration inventory is empty

**Work:** Audit all production verification paths, runtime specs, public docs,
examples, fixtures, imported summaries, and cached certificates. Enable the
new authority semantics globally; current count without authority now fails
uniformly. Remove temporary per-project selection and reject incompatible old
certificates/caches. Keep old implementation code unreachable for this
checkpoint if that makes the switch independently reviewable.

**Exit gate:** The full corpus passes with legacy execution disabled. Tests
prove there is no fallback and field presence no longer selects countability.
There are zero active `guarded_by` consumers except targeted rejection tests.
Only after this gate may the old implementation be deleted.

### 12. Delete legacy machinery in separately green cleanup commits

**Work:** Remove the unreachable implicit-population access and count-in-body
classification, field-based countability checks, and obsolete population mutex
custody. Remove `guarded_by` parser/lowering/kernel metadata in a separate
reviewable commit, retaining a useful diagnostic for the retired spelling.
Remove migration metadata and dead tests only after their replacement coverage
is recorded. Update historical design statuses and public resource docs.

**Exit gate:** Source and test inventory confirms no old permission path,
scaffolding, or active syntax remains. The full gate and affected proof audits
pass. Mark the authority migration complete and resume the concurrency demo
on the new foundation.

An identified-slot example should test that a field-bearing member can change
its privately owned memory while the control resource stays closed, provided
that update changes no population invariant. Removing the slot requires its
membership and authority. General sums over member fields, mutable ghost maps,
fractional/persistent fragments, atomic refcounts, and arbitrary user-defined
algebras are follow-up scope, not prerequisites for this migration.

## Small intended regressions

Use a sequential object with C helpers that increment and decrement `refs`.
With exposed control authority, retain produces one reference and release
consumes one; their caller proves the exact stored count. The unchanged helper
body must fail if its contract omits authority or a decrement omits the spent
reference. These are target migration regressions, not alleged current proofs
of false.

Additional hostile cases must reject:

- Current count observations without authority, including through predicates,
  snapshots mislabeled as current, field-bearing members, and opaque helpers.
- Duplicate or overlapping authority, mismatched population arguments, stale
  authority after retirement/reinitialization, and alias-based duplication.
- Creation/deletion while control is closed elsewhere, including inside a
  worker or hidden wrapper; double consumption at scope close and return.
- Counter writes without restored count equality, stale invariant facts after
  a call/acquisition, and final free while any reference remains outstanding.
- Independently opening the same exclusive C memory through two ordinary
  instances, and retaining old population-body access through compatibility code.

Positive counterparts must preserve transfer without authority, quantity
regrouping, field-bearing member counting, private-memory access, independent
populations, and harmless historical observations.

Diagnostics should name the missing source resource/fact, for example
`Requires owns authority(reference(p))`, the reference required for consumption,
or the counter equality that failed restoration. Do not expose internal ledger
or algebra names as substitutes for an actionable obligation.

## Acceptance criteria

- Current count observations and population transitions have explicit checked
  authority dependencies; ordinary unrelated resources require no authority.
- Resource-type meaning is independent of proof fields. Ordinary contents obey
  normal exclusive ownership; members do not implicitly share one memory body.
- All migrated examples above retain their C and claims. The new shared-refcount
  example verifies through ordinary runtime and resource contracts, with no
  refcount-specific mutex rule. Original safety regressions remain covered.
- `guarded_by` and the superseded counting/access classifications are removed,
  including dead scaffolding, stale documentation, and bypasses in certificates.
- Kernel tests check hostile updates independently of tactics. Verify first,
  then profile, expand/reverify, and audit affected proofs. Current observations
  stay fresh across calls, lock acquisitions, and joins.
- Deterministic scaling tests vary members, transfers, and unrelated state.
  Updates must operate on the supplied pieces and indexed population state,
  not scan every owner or clone whole environments/histories. Work is roughly
  linear in explicit source/certificate size, up to indexing factors.
- `scripts/check.sh` passes; docs distinguish implemented rules from deferred
  generalizations. The concurrency issue then resumes on this foundation.

Delete this issue and its index entry when the migration, regressions,
examples, and documentation are complete.
