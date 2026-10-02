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

### Milestone 1: Complete bounded pool (7–9 chunks)

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

#### Current milestone 1 checkpoint

Return through a two-authority control now has direct and nested regressions:
`mdtests/authority_pool_control_return_full.md`. They consume the exact member,
return its private object and a slot, preserve both invariants and the ordinary
`valid_pool(pool)` predicate, and retain a caller-owned neighboring slot. Import validation rejects absent custody,
duplicate inputs, and a member from the wrong pool. Signed sum checks preserve
all required operand domains, including reversed summands.

`mdtests/authority_pool_control_init_nested.md` verifies standalone initialization
with an arbitrary nonnegative capacity and a nested initialization at capacity
two. Numerical batches now compose with unit exchanges in imported unary
populations; zero has no member rights. Symbolic batches forwarded through
another opaque helper still need support. These tests do not complete the
original bounded-pool migration.

The two-object checkout/write/return sequence now has a reduced regression in
`mdtests/authority_pool_control_two_members.md`, including private writes with
control closed, two exact custodies, opposite-order returns, and a final slot
quantity of two. Positive fixed exclusive memory footprints justify exact
member uniqueness; this follows ownership and does not use proof-field presence
to determine countedness. Wrong-member and double-spend tests preserve the
separate count and custody checks. Symbolic batches and the original
resize/transfer/cleanup paths remain to migrate.

The original C is unchanged. Do not replace these pipelines with locally
allocated synthetic pools or weaken their final claims to avoid the gaps.

The checkout definedness reduction is now checked without an authority or
counter-cache change. `authority_count_defined_through_control.md` opens a
control with an arbitrary entry count, a nonnegative counter, and equality
between the counter and the wildcard population count. An explicit arithmetic
step supplies `counter >= 0`; rewriting the count to the equal counter then
transports `defined(counter + 1)` to `defined(count(...) + 1)`. Its two smart
sites expand and reverify. `authority_count_defined_at_max_rejected.md` checks
that the same control cannot justify an increment at `2147483647`.

`authority_pool_checkout_original_bound.md` now verifies the original
`pool_checkout.c` verbatim under authority semantics. It derives increment
safety from one available slot, the nonnegative counter, and the defined
capacity invariant; no extra counter-bound requirement is added. The proof
preserves `valid_pool` and checks the counter, capacity, and both population
count changes. All seven smart sites expand and reverify. Its companion
`authority_pool_checkout_without_slot_rejected.md` rejects the unavailable-slot
case with `Requires 1 <= count(pool_slot(pool))`.

The original-bound checkout regression now also proves direct and nested
ordinary helper calls. Their contracts retain the same control, slot/object
consumption, member production, count deltas, and `valid_pool` claim, without
`checked_out < 2147483647`. Each call's proof opens the control, proves count
increment definedness from the available slot, and closes it before the C call.
No verifier or authority change was needed. The missing-slot helper regression
pins rejection at call transfer; its current diagnostic is
`population call transfer refused: MissingMembers`.

The symbolic-quantity entry prerequisite now retains the nonnegative guard
implicit in `owns n of slot(pool)` in the checked proof context. Previously,
setup used that guard and then dropped it before checking the entry boundary,
which could trigger an assertion. `authority_symbolic_quantity_entry.md`
proves the direct authority contract without a redundant `requires 0 <= n`;
its negative-call companion checks that the shared quantity guard still rejects
a negative caller quantity using legacy call semantics. Checked entry failures
now return a bounded diagnostic instead of asserting. This does not add
symbolic batch transfer support.

Field-valued quantities now read through explicitly required folded controls.
`authority_control_quantity_read.md` checks `owns pool->capacity of slot(pool)`
in both clause orders and proves the implicit nonnegative entry guard. Its
negative companions reject authority without memory and a different pool's
control. The projection grants read views only; a zero owned quantity cannot
expose the body. It does not open authority or import mutable body custody.
The same quantity setup is used by source entry, certified entry, and derived
loop-frame setup. Deterministic regressions cover many quantity clauses and
unrelated resource definitions; definition lookup is indexed.

Direct cleanup now has an authority regression in
`authority_pool_control_cleanup.md`, using `pool_destroy.c` verbatim. It
consumes the arbitrary entry-capacity slot batch, restores capacity zero,
checks the private-object population is empty, retires both authorities, and
returns ordinary pool storage. Zero-capacity cleanup uses the same proof.
Imported retirement now checks exhausted member custody and a proven current
global zero instead of requiring a unit final release. Negative companions
reject both an unspent batch and a nonzero global population with no locally
owned members; writing capacity zero does not satisfy either obligation.

The next small slice is symbolic batch helper transfer: pass cleanup's control
and complete slot quantity through an ordinary helper contract, preserving the
retirement evidence at return. Symbolic grow/shrink and two-pool transfer remain
separate. The original bounded-pool project still uses legacy counting and is
not migrated as a whole. The speculative cache repair remains removed; the
checkout proofs required no count-model or authority change.
Missing facts inside `open(...)` report `Requires f`.

### Milestone 2: Finish member identity and proof fields (3–4 chunks)

1. Define/check population occurrence identity independently of proof fields;
   equal parameters must not merge distinct member states.
2. Support count observations and real birth/consumption for individually
   identified field-bearing members, including exact/wildcard boundaries.
3. Support ordinary helper transport and member-only private updates. Prove an
   identified-slot example while its authority-bearing control stays closed.
4. If needed, finish replacement negatives for legacy field-based countability;
   distinguish unsupported symbolic quantity syntax from family countability.

**Exit gate:** Two disjoint field-bearing members preserve their identities and
private state; exclusive-memory conflicts and unauthorized transitions fail.
No new-model decision uses field presence to select countability. Do not require
symbolic quantities of heterogeneous instances or general sums over fields.

### Milestone 3: Migrate remaining sequential accounting (3–4 chunks)

1. Migrate remaining numeric/symbolic quantity groups and local contribution
   consumption, retaining scope-close and return single-spend checks.
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
