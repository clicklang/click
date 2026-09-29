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

1. **Population establishment and retirement.** Allocate authority with a fresh
   logical identity and justified initial members/count. Folding a wrapper
   cannot create authority. Establish how existing members can be enrolled,
   or initially restrict establishment to a fresh population. Prevent a second
   authority, re-enrollment of existing units, and resurrection by pointer reuse.
   Retirement/reclamation must account for outstanding members and loans.
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

Start with explicit authority for tracked populations. Do not invent an
implicit sequential-authority fallback to keep old examples passing. Keep
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

## Ordered implementation and examples

Keep each landed checkpoint green. Preserve the original C and properties;
migrate sidecars and checker rules rather than weakening assertions or rewriting
programs. Temporary implementation coexistence must have a removal endpoint,
not become a permanent alternate public counting mode.

1. **Specify and implement authority fundamentals.** Establishment, identity,
   ownership transfer, current observation, and checked member updates. Test
   the permission rules independently of mutexes. Remove field-based semantic
   classification as ordinary instances and tracked membership are separated.
2. **Migrate sequential refcount.** Preserve
   [the complete refcount example](../examples/refcount/README.md): initialize,
   retain, symbolic retain/release, nonfinal release, final free, allocation
   failure, and callers. References are members; control owns the C counter,
   allocation/lifetime obligations as appropriate, and population authority.
3. **Migrate shared-parent lifetimes and bounded pool.** Preserve
   [both parent destruction orders](../mdtests/shared_heap_population_lifecycles.md),
   surviving-parent reads, and final reclamation. Preserve
   [bounded pool](../examples/bounded-pool/README.md) checkout/return, resizing,
   zero capacity, wildcard counts, and cross-pool transfer. Pool object memory
   remains individually owned; opening it need not acquire pool authority.
4. **Migrate contribution and join accounting.** Preserve
   [sequential exact two](../mdtests/counted_resource_contribution_counter.md),
   [local mutex conservation](../mdtests/population_conservation_local_mutex.md),
   and existing abstract worker-ticket regressions. Worker consumption must
   obtain authority or use an explicitly justified deferred transfer; a join
   cannot retroactively authorize an invalid worker transition. Preserve either
   join order, create failures, and rejection of premature exact observations.
5. **Verify a mutex-protected shared refcount.** Freeze a small ordinary C
   program with two users, a retained owner reference, locked retain/release,
   and final reclamation after users finish. It must keep the object and its
   mutex alive before acquisition, reject reclamation while references remain,
   and free exactly once. Model failure cleanup. This is the migration's
   concurrency acceptance example, not an atomic-refcount or lock-free claim.
6. **Remove superseded machinery and document the result.** Delete the
   count-in-body semantic switch, single-member access to a shared invariant,
   and population-specific mutex custody made redundant by ordinary authority
   transfer. Remove `guarded_by`. Migrate every affected example and fixture;
   revise public resource docs and historical design statuses to identify the
   replacement. Then unblock the concurrency demo's exact worker counter.

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
