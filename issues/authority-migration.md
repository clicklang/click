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

The legacy path, still used by the mutex and worker groups, mixes independent
concerns:

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

## Milestones and chunks

Build support additively, migrate consumers, then switch and remove the old
model. Keep the original C and its properties fixed.

A **chunk** is one missing capability or one small consumer group, with focused
positive and negative regressions, independent kernel/certificate checks where
they apply, documentation, and a green full gate. It is roughly one reviewable
pull-request increment. A **milestone** is four chunks ending in an acceptance
demonstration; it is not permission to combine unrelated verifier repairs into
one large patch. Do not expand scope to fill a planned chunk, and do not hide
an extra capability inside one: if a chunk needs more, split it and record the
change here.

### Status

Milestones 1–4 are complete, building on the foundation that the earlier
checkpoints 0–5 delivered. Authority semantics now cover sequential refcount,
shared-parent ownership, the bounded pool, field-bearing named members,
every sequential population consumer, and mutex-held authority controls.
Milestone 6 chunk 1, the worker protocol freeze, is also complete. The approved
[object-anchored lifetime protocol](../docs/internals/authority-establishment-review.md)
governs establishment and retirement. The
[consumer inventory](../docs/internals/authority-migration-inventory.md) lists
the remaining legacy groups and keeps the per-milestone evidence; this issue
holds only the plan.

| Milestone | State | Exit demonstration |
| --- | --- | --- |
| 1. Bounded pool | Complete | Original pool C verifies initialization, checkout/return, resize, transfer, and cleanup |
| 2. Member identity and proof fields | Complete | Count identified members without erasing private proof state |
| 3. Remaining sequential accounting | Complete | All sequential inventory groups use authority without fallback |
| 4. Mutex-held authority controls | Complete | Ordinary protected controls replace counted-population mutex custody |
| 5. Retire `guarded_by` associations | Complete, except two worker fixtures moved to milestone 6 | No active `guarded_by` consumer; associations come from checked initialization |
| 6. Concurrent lifetime and worker accounting | Chunk 1 complete; 3 chunks | Shared refcount and worker accounting verify through ordinary transfers |
| 7. Sole default and legacy removal | 4 chunks | One checked counting model remains; old machinery and `guarded_by` are deleted |

The remaining plan is **four milestones of four chunks**. These are planning
estimates, not promises. The milestone 6 worker protocol is now frozen and
needs no new syntax or kernel algebra. Tooling repairs may still add chunks.

What remains on the legacy path is 21 worker count fixtures; two of them are
also the last `guarded_by` fixtures. One deliberate
legacy control, `fold_negative_quantity_legacy_control.md`, stays until
milestone 7. The inventory names every file.

### Dependency order

- Milestone 4 chunk 1 (protected control deposit and acquisition) is the
  prerequisite for the rest of milestones 4, 5, and 6.
- After it lands, milestone 4 chunks 2–4 and milestone 5 are independent and
  may interleave. `guarded_by` replacement needs ordinary initialization and
  transfer of a control, not population authority.
- Milestone 6 chunk 1 is a documentation-only design freeze. Land it early,
  alongside milestone 4, because its answer may constrain milestone 4's helper
  contracts. Implementation chunks of milestone 6 wait for milestone 4.
- Milestone 7 starts only when the inventory's legacy list is empty.

### Rollout safeguards

- Keep the existing corpus green. Do not quarantine proofs, weaken claims, or
  discard negatives to force a migration through.
- Retain legacy only for explicitly unmigrated verification units. Authority
  proofs must never retry under legacy rules. All reachable contracts, imports,
  caches, and certificates must agree on the selected model; reject unchecked
  mixed boundaries. Temporary project selection is not a permanent keyword.
- When a group leaves legacy, record in the inventory its fixtures, original
  claims, positive and negative replacements, and verify/expand/audit evidence.
  Migrate dependencies together.
- Use focused checks for each chunk; PR CI and the merge queue run the full
  `scripts/check.sh`. Use the documentation gate for prose-only chunks. Verify
  before profiling, expanding, or auditing.
- Keep failed experiments isolated and retain green checkpoints. Fix tooling
  correctness, bounds, and diagnostics before building further features. Add
  deterministic multi-size scaling tests for performance-sensitive changes.
- Discuss any additional surface syntax before implementing it. Do not invent
  implicit sequential authority, revive `<>`, or introduce sum-specific built-ins.

### Milestone 4: Mutex-held authority controls

1. **Deposit and acquire a control.** Checked initialization deposits an
   ordinary authority-bearing control in a mutex. Lock returns it with the
   acquisition guard; unlock requires it back with its facts restored. The same
   control remains usable sequentially without a mutex. Regressions reject
   unlock without the restored invariant, a member alone exposing the control,
   a wrong mutex, and stale initialization. A kernel check confirms that this
   path uses no counted-population mutex custody. **Complete:** the control
   declares a proof field so that it is a named instance; the inventory's
   milestone 4 record lists the evidence.
2. **Acquiring and releasing helpers.** Independently checked helpers lock and
   unlock through existing `owns`/`consumes`/`produces`, including replacement
   state and lifetime holds. Count observations after an acquisition or a
   helper return are fresh; earlier facts remain historical only. Reject stale
   observations, wrong mutexes, and missing state. **Complete** for helpers that move the
   guard and control between the mutex and their caller. A helper that opens
   the acquired control itself, such as a locked retain or release, needs a
   fresh opaque population per acquisition and a caller-side member delta.
   That is split out of this chunk; milestone 6 chunk 4 depends on it.
3. **Protected bodies and local conservation.** Migrate the six
   `mutex_population_*` fixtures and both `population_conservation_local_mutex*`
   fixtures. These also use `guarded_by`, so they migrate both concerns at
   once. The missing-value-relation and bad-increment cases must still fail.
   **Complete** for six of the eight. `mutex_population_separate_body.md` and
   `mutex_population_missing_value_relation.md` count contributions consumed
   by `pthread_create` workers, so they move to milestone 6 chunk 3.
4. **Held/unheld helpers and closeout.** Migrate the seven `population_mutex_*`
   fixtures: held and unheld helper access, unheld direct reads, complete
   publication and release, hidden units, and the second custodian. Update the
   mutex internals documentation. **Complete:** all seven select authority;
   the inventory records each replacement refusal.

**Exit gate:** Lock gives control ownership, unlock requires its restored
invariant, and a member alone cannot expose it. No authority proof or helper
certificate uses counted-population mutex custody. Parity, ordinary mutex
helpers, and all earlier migrations stay green.

### Milestone 5: Retire `guarded_by` associations

Requires milestone 4 chunk 1. Keep the parser and kernel metadata until
milestone 7; this milestone removes consumers, not the syntax.

1. **Core association semantics.** Migrate `guarded_resource_*` (3),
   `modeled_pthread_mutex_*` (3), `mutex_lifetime_named*` (2),
   `mutex_resource_quantity_requires_conservation.md`, and the guarded
   `mutex_unlock_missing_guard_and_invariant.md`. Together these cover
   authenticated protected types, initialization identity, folded restoration,
   wrong-mutex and stale-state rejection, early destroy, and parent interference.
   They set the replacement pattern for the remaining families. **Complete:**
   the inventory's milestone 5 record lists each outcome; the wrong-mutex
   refusal moves to a typed-use companion fixture.
2. **Guard family.** Migrate the 27 guarded `mutex_guard_*` fixtures. Inspect
   each `expect` block; the family contains both passes and refusals. This chunk
   is mostly mechanical once chunk 1 lands, and may land as two increments.
   **Complete:** all 27 keep their outcomes and messages.
3. **Use, helper-transfer, and runtime-contract families.** Migrate the 10
   guarded `mutex_use_*`, 3 guarded `mutex_helper_transfers*`, and 6
   `runtime_mutex_contract_*` fixtures. **Complete:** all keep their outcomes.
4. **Specification, documentation, and audit.** Update
   `src/languages/c/modeled_pthread_spec.md`, `docs/concepts/resources.md`,
   `docs/internals/mutex-resource-contracts.md`,
   `docs/internals/concurrency-contracts-and-diagnostics.md`,
   `docs/internals/resource-parameters.md`, and the concurrency design probe.
   The discovery search then finds `guarded_by` only in migration records.
   **Complete:** the teaching documents describe association by
   initialization. The trusted specification keeps one sentence marking the
   annotation deprecated, because the parser and kernel accept it until
   milestone 7 removes them. The two worker `mutex_population_*` fixtures
   still use it and migrate with milestone 6 chunk 3.

**Exit gate:** No fixture, example, specification, or active document uses
`guarded_by`. Wrong-association, stale-initialization, and missing-state
negatives retain their refusals through ordinary initialization and transfer.

### Milestone 6: Concurrent lifetime and worker accounting

1. **Freeze the worker protocol (documentation only; land early).** Specify
   how authority and members cross thread creation, worker contracts, create
   failure, and join for workers that hold no lock. A worker either possesses
   authority or uses a specifically justified deferred transfer; join cannot
   retroactively authorize birth or consumption. Map each of the 19 worker
   fixtures to the protocol. If it needs new surface syntax or kernel algebra
   beyond existing transfers, stop and discuss before coding. **Complete:** the
   [worker authority protocol](../docs/internals/worker-authority-protocol.md)
   uses only existing transfers and maps all 19 fixtures. It also lists the
   properties that milestone 4 must provide.
2. **Lifetime transport and abstract workers.** Implement the smallest
   protocol with independent certificate checks and misuse regressions,
   rejecting premature observation and reclamation. Migrate the nine abstract
   worker and join fixtures.
3. **Shared worker population.** Migrate the ten shared-population fixtures
   and the two worker `mutex_population_*` fixtures moved from milestone 4:
   create failure, either join order, retained units, symbolic joins, and
   early, stale, observer, and missing-unit refusals.
4. **Shared-refcount acceptance example.** Freeze and verify a small ordinary
   C program with two users, a retained owner reference, locked retain/release,
   and final reclamation after the users finish. Cover creation failure and
   both completion/join orders.

**Exit gate:** References keep the object and mutex alive before acquisition;
population updates preserve framed ownership; reclamation occurs exactly once
after the necessary references and loans are recovered. Every count consumer
has a new-model replacement. Verify, expand/reverify, and audit pass without a
refcount-specific mutex rule. The final exact-two shared-worker counter remains
a subsequent concurrency-demo task. Atomic or lock-free refcounting is out of
scope.

### Milestone 7: Sole default and legacy removal

1. **Audit and switch.** Confirm the inventory's legacy list is empty, then
   audit production paths, runtime specifications, public documentation,
   imports, summaries, caches, and certificates. Make authority the sole
   execution model: reject unauthorized current counts uniformly and
   incompatible old caches and certificates, and remove temporary project
   selection. Retire `fold_negative_quantity_legacy_control.md` against its
   authority replacement. Keep old code unreachable in this chunk so the
   switch is independently reviewable.
2. **Delete legacy population machinery.** Remove implicit population-body
   access, count-in-body classification, field-based countability, and
   counted-population mutex custody, with replacement coverage recorded first.
3. **Remove `guarded_by`.** Remove parser, lowering, and kernel metadata,
   retaining a useful retired-spelling diagnostic and its regression.
4. **Documentation and close.** Update public resource documentation, the
   glossary, examples, and historical design statuses; remove migration
   metadata and dead tests. Complete this issue and resume the concurrency demo.

**Exit gate:** The full corpus passes with no legacy execution or fallback, no
old permission machinery, and no active `guarded_by` consumer. Tests prove that
field presence no longer selects countability.

## Scope boundary

General aggregate invariants over proof fields, mutable ghost maps, fractional
or persistent fragments, arbitrary user-defined algebras, and atomic refcounts
are follow-up projects. General controls with more than two authorities,
partially fixed population patterns, and symbolic exact subsets are not migration
prerequisites unless an unchanged acceptance example demonstrates a need.

The following shapes are known unsupported under authority semantics. They are
not prerequisites for any milestone above, and milestone 7 must not treat them
as unfinished migration work:

- Splitting a coalesced symbolic batch, extending imported symbolic entry
  custody, or mixing a symbolic input or spend with numerical effects.
- Symbolic quantities of heterogeneous field-bearing instances and general sums
  over member fields.
- Named-member birth or consumption through assumed (bodiless) interfaces,
  which supply no body certificate for the population effect.

If an acceptance example or a later project needs one of these, discuss it as
separate work rather than widening this migration.

The shared-parent detach contract that consumes two units and produces one is
not in this list: its proof verifies, but no caller can apply it. That is a
filed defect, [a verified two-to-one quantity contract cannot be applied](../bugs/a-verified-two-to-one-quantity-contract-cannot-be-applied.md),
not a scope decision. The migrated fixture uses a stronger natural contract in
the meantime.

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
