# P1: Authority migration

## Goal and dependency order

Replace implicit counted-population access with explicit population authority.
Keep `count(...)` as an observation, make resource types consistent regardless
of proof fields, and remove `guarded_by`. Use ordinary resource composition and
`owns`/`views`/`consumes`/`produces` to connect population accounting to memory
and mutex operations. Do this migration before extending the
[concurrency demo](concurrency-demo.md) to exact shared-worker accounting.

This is the selected direction, implemented additively for the migrated groups
below. It is not a claim that legacy sequential proofs are unsound. It supersedes the whole-population mutex-custody
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

### Authority interface

The implemented surface uses ordinary resources and the built-in `authority`:

```text
resource reference(p: struct object*) {
}

resource control(p: struct object*) {
    owns p->refs;
    owns authority(reference(p));
    fact p->refs == count(reference(p));
}
```

`authority(reference(p))` is a built-in resource, exclusively held for
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

### Permission rules and remaining design boundaries

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

## Milestones and chunk size

Build support additively, migrate consumers, then switch and remove the old
model. Keep the original C and its properties fixed. A chunk is one missing
capability or one small consumer group, with focused positive and negative
regressions, independent kernel/certificate checks where appropriate,
documentation, and a green full gate. A milestone is an acceptance demonstration,
not permission to combine unrelated verifier repairs into a large patch.

The rough remaining budget is **26–34 chunks across six milestones**. Including
completed foundations and earlier migrations, the whole effort is approximately
50 chunks, with uncertainty of about ten. Historical changes were not uniformly
sized; these are planning estimates, not measured effort or promises. Tooling
repairs may add chunks. Do not expand scope merely to fill a predicted number.
One milestone may use one PR with several green commits when it remains coherent.

### Completed foundations

The [consumer inventory](../docs/internals/authority-migration-inventory.md)
records migrated groups and regressions. The approved
[object-anchored lifetime protocol](../docs/internals/authority-establishment-review.md)
checks actual heap/automatic-object creation, once-per-lifetime establishment,
explicit transport, empty retirement, and dependencies preventing early free.

Kernel and source support now check authority custody, current versus historical
counts, real birth/consumption, private-body access, and independently checked
ordinary helper contracts. Helper populations enter with arbitrary totals and
no creator rights. Sequential refcount, symbolic batches, and shared-parent
ownership have migrated. Field-free wildcard populations support concrete-member
creation, consumption, cross-pool moves, private memory and invariants, contained
ordinary resources, and exact member observations. A control can package two
same-anchor authorities with counter facts; direct and nested checkout preserve
that control and caller-retained slots. No new parameter syntax is needed.

Named proof-field population identity, the original bounded-pool sidecar,
remaining sequential groups, mutex/worker migration, and the default switch
remain unfinished. Earlier checkpoint numbers 0–5 correspond to the completed
foundation; unfinished checkpoint 6–12 work is reorganized below. Detailed
historical evidence belongs in the inventory, not a second competing roadmap.

| Milestone | Estimated chunks | Exit demonstration |
| --- | --- | --- |
| 1. Bounded pool | 7–9 | Original pool C verifies initialization, checkout/return, resize, transfer, and cleanup |
| 2. Member identity and proof fields | 3–4 | Count identified members without erasing private proof state |
| 3. Remaining sequential accounting | 3–4 | All sequential inventory groups use authority without fallback |
| 4. Mutex integration | 4–5 | Ordinary protected-control transfers replace population mutex special cases |
| 5. Concurrent lifetime and accounting | 5–7 | Shared refcount and worker accounting cover interference, joins, failure, and cleanup |
| 6. Sole default and legacy removal | 4–5 | One checked counting model remains; `guarded_by` and old machinery are removed |

### Rollout safeguards

- Keep the existing corpus green. Do not quarantine proofs, weaken claims, or
  discard negatives to force a migration through.
- Retain legacy only for explicitly unmigrated verification units. Authority
  proofs must never retry under legacy rules. All reachable contracts, imports,
  caches, and certificates must agree on the selected model; reject unchecked
  mixed boundaries. Temporary project selection is not a permanent keyword.
- Record each group's selected path, original claims, dependencies, and
  replacement regressions in the inventory. Migrate dependencies together.
- Run focused checks and unpiped `scripts/check.sh` before submitting executable
  work; use the documentation gate for prose-only checkpoints. If upstream
  moves, update the branch and rerun affected gates. Use fork PRs and the merge
  queue; never integrate directly into upstream master.
- Keep failed experiments isolated and retain green checkpoints. Fix tooling
  correctness, bounds, and diagnostics before building further features. Add
  deterministic multi-size scaling tests for performance-sensitive changes.
- Discuss any additional surface syntax before implementing it. Do not invent
  implicit sequential authority, revive `<>`, or introduce sum-specific built-ins.

### Milestone 1: Complete bounded pool — complete (7–9 planned chunks)

**North star:** [bounded pool](../examples/bounded-pool/README.md), with its
original C and claims. Missing capabilities get small regressions before the
whole example depends on them. Chunk order may change when a dependency becomes
clear; combine already-supported steps rather than manufacturing extra changes.

1. **Return through a control.** Import a concrete wildcard input member under
   authority held inside the pool control. Consume it through direct/nested
   helpers, returning its private memory and a slot. Check arbitrary entry
   totals, retained neighbors, wrong identities, and the actual decrement.
2. **Object ownership boundary.** Check which original pool paths need a local
   object bridge. Where genuinely needed, make C-created automatic objects
   transferable through ordinary ownership without rewriting C. The existing
   stack-object rejection is a separate reduced regression, not a reason to
   add irrelevant ownership machinery to external-pointer pipelines.
3. **Initialization and cleanup.** Helpers receive explicitly passed authority,
   package both populations with initialized pool memory, and later return or
   retire it through ordinary contracts. Establishment remains creator-only;
   `pool_init` receiving an external pointer cannot invent creation rights.
   Cover arbitrary inputs, empty populations, duplicate establishment, and
   nonempty retirement. Preserve the original zero/destroy claims.
4. **Symbolic slot quantities.** Support initialized capacity and grow/shrink
   batches through the two-authority control, including zero quantities and
   signed arithmetic bounds. Preserve retained members and reject unowned
   consumption and overflow. No symbolic wildcard subset machinery unless used.
5. **Multiple checked transitions.** Admit the bounded set of member effects
   needed for transfer: return the source slot, consume the destination slot,
   and move the concrete object membership. Independently authenticate each
   effect, authority, identity, quantity, and body exchange.
6. **Two-control transfer.** Restore both pool invariants after the unchanged
   two-counter C operation. Preserve framed members and private object memory;
   reject wrong pools, aliases without proof, missing updates, and double spend.
7. **Checkout/return pipeline.** Migrate the original pipeline, retaining private
   object writes while control stays closed and final values 11/22. It must not
   need pool authority just to modify the member's private contents.
8. **Zero, resize, and transfer pipelines.** Migrate the remaining original pool
   claims, update README/contracts/inventory, and audit successful proofs.

**Exit gate:** Every original bounded-pool claim verifies with explicit authority;
all C files are unchanged. Verify, expand/reverify, and audit affected proofs;
focused positives/negatives and the full gate pass. Private memory access remains
ordinary member ownership. Any capability not actually required by these claims
stays a separate future task rather than expanding this milestone.

#### Milestone 1 completion checkpoint

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
cache repair remains removed. Milestones 1 and 2 are complete; milestone 3 is next.

### Milestone 2: Finish member identity and proof fields — complete (four slices)

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
   field-count rejection fixtures remain controls.

**Exit gate passed:** Two disjoint field-bearing members preserve identity and
private state; exclusive-memory conflicts and unauthorized transitions fail.
Field presence does not select authority-mode family countability. No new
surface syntax or changes to existing C were needed. The full `scripts/check.sh`
gate passed 4,723 unit/integration tests and 190 fixture tests; all 48 new
named-member expansion-audit sites passed.

**Explicit remaining boundaries:** Named-member creation/consumption through
helpers with explicit authority still needs checked lifecycle effects. Calls
cannot silently remove or add a tracked member without updating the ledger;
unsupported transitions are rejected. Symbolic quantities of heterogeneous
instances, algebraic/list field descriptions, and general sums over fields are
not implemented. Local lifecycle operations and preserving helpers are supported.
These limits do not restrict ordinary uncounted named resources.

### Milestone 3: Migrate remaining sequential accounting (3–4 chunks)

**First small slice:** The constant-quantity fixtures now use authority semantics.
`let_bound_constant_quantity.md` packages allocation, counter memory, and
authority in an ordinary control; its contract still consumes the quantity
selected by `let k = 2`. `fold_rejects_a_negative_quantity.md` preserves the
zero/negative boundary with a separate reference family and owned counter
memory. Negative coefficients report the required nonnegative fact rather
than `InvalidQuantity`. C source is unchanged.

**Next boundaries found:** A symbolic helper birth followed by a unit birth is
currently rejected because numeric and symbolic ledger effects cannot mix.
The reduced reproduction is the original pair of
`population_symbolic_increment_{bounded,overflow}.md` fixtures with explicit
authority and defined-addition contracts.

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

1. Migrate remaining numeric/symbolic quantity groups and local contribution
   consumption, retaining scope-close and return single-spend checks.
   Before migrating named-member lifecycle helpers, extend their checked
   authority effects for explicit helper birth/consumption; milestone two
   supports preserving transport and local lifecycle operations only.
2. Migrate predicates, loops, current/old snapshots, and contract observation
   boundaries without permitting count facts to manufacture authority.
3. Migrate sequential exact-two accounting and dependent helper groups.
4. Finish residual sequential consumers and replacement diagnostic/negative
   coverage from the inventory, if the earlier groups do not cover them.

**Exit gate:** Every sequential consumer has a checked authority replacement;
no group is silently skipped or weakened. Mutex and worker legacy groups remain
explicitly listed for their own milestones.

### Milestone 4: Integrate authority with mutexes (4–5 chunks)

1. Deposit an ordinary authority-bearing control during checked initialization;
   lock returns it, unlock requires it with restored facts.
2. Support independently checked acquiring/releasing helpers using existing
   `owns`/`consumes`/`produces`, including replacement state and lifetime holds.
3. Check fresh count observations after possible interference and reject stale
   observations, wrong mutexes, missing state, and stale initialization.
4. Migrate held/unheld population helpers and local-conservation groups.
5. Migrate active `guarded_by` associations to ordinary initialization/transfer
   in dependency groups; retain its parser until the final removal milestone.

**Exit gate:** These proofs/certificates use no special counted-population mutex
custody. A member alone grants no protected control access. Parity, ordinary
mutex helpers, and all earlier migrations stay green.

### Milestone 5: Concurrent lifetime and worker accounting (5–7 chunks)

1. Check authority/member lifetime transport through create, worker contracts,
   and join, rejecting premature observations and reclamation.
2. Freeze the no-lock worker accounting protocol. Workers must possess authority
   or use a specifically justified deferred transfer; join cannot retroactively
   authorize birth/consumption. Discuss a substantive design gap before coding.
3. Implement the smallest justified protocol with independent certificate and
   misuse regressions, if the existing transfers cannot express it.
4. Migrate abstract tickets/contributions, retained units, and symbolic joins.
5. Verify a mutex-protected shared-refcount C example with two users, a retained
   owner reference, locked retain/release, and final reclamation.
6. Cover create failures, either completion/join order, early/stale count
   refusals, and exact cleanup across dependent worker fixtures.
7. Finish remaining concurrent consumer groups and audits if necessary.

**Exit gate:** Distributed references preserve object/mutex lifetime, population
updates preserve framed ownership, and final reclamation occurs exactly once.
Every count consumer has a new-model replacement. Verify/expand/reverify/audit
pass without a refcount-specific mutex rule. The final exact-two shared-worker
counter remains a subsequent concurrency-demo task, not an additional authority
migration gate. Atomic or lock-free refcounting is out of scope.

### Milestone 6: Switch the default and delete legacy machinery (4–5 chunks)

1. Audit production paths, runtime specs, public docs, imports, summaries,
   caches, and certificates against the now-empty legacy consumer inventory.
2. Make authority the sole execution model; reject unauthorized current counts
   uniformly and incompatible old caches/certificates. Remove temporary project
   selection. Keep old code unreachable until this switch is independently green.
3. Delete implicit population body access, count-in-body classification,
   field-based countability, and obsolete counted-population mutex custody.
4. Remove `guarded_by` parser/lowering/kernel metadata, retaining a useful
   retired-spelling diagnostic and migrated wrong-association regressions.
5. Remove obsolete migration metadata/dead tests and update historical statuses
   and public documentation if this does not fit the preceding cleanup commits.

**Exit gate:** Full corpus passes with no legacy execution/fallback, old permission
machinery, or active `guarded_by` consumer. Replacement coverage is recorded
before old tests disappear. Complete this issue and resume the concurrency demo.

## Scope boundary

General aggregate invariants over proof fields, mutable ghost maps, fractional
or persistent fragments, arbitrary user-defined algebras, and atomic refcounts
are follow-up projects. General controls with more than two authorities,
partially fixed population patterns, and symbolic exact subsets are not migration
prerequisites unless an unchanged acceptance example demonstrates a need.

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
