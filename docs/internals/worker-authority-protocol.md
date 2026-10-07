# Worker authority protocol

This page specifies how population authority and members cross
`pthread_create` and `pthread_join` for workers that hold no lock. Milestone 6
chunk 1 of `issues/authority-migration.md` froze it, and chunks 2 and 3
implemented it and migrated every worker fixture; the
[implementation](#implementation) section says how. The
[object-anchored population authority](authority-establishment-review.md)
page holds the sequential rules this protocol extends, and the
[consumer inventory](authority-migration-inventory.md) records migration
evidence.

The protocol needs no new surface syntax and no new kernel algebra. A thread
boundary uses the same exclusive authority resource, the same ordinary member
transfers, and the same checked `fold`/`unfold` member transitions as a
verified sequential call. Thread creation behaves like the entry of a call
whose return is delayed until a checked join.

## Rules

1. **One holder.** `authority(R(p))` stays one exclusive resource. At any
   moment it is owned by exactly one thread, held in one mutex escrow
   (milestone 4), or retired. No operation splits, copies, or shares it.
2. **Only the holder changes or observes the population.** A thread observes
   a current `count(R(p))`, folds a new member, or unfolds an existing member
   only while it owns the matching authority. This applies inside workers
   exactly as in sequential code.
3. **Authority crosses a thread boundary only as a task resource.** A worker
   obtains authority in exactly two ways: its contract transfers it with
   `owns authority(R(p))`, or it acquires a mutex-held control that contains
   it (milestones 4 and 6). No other route gives a worker authority. A worker
   contract borrows authority with `owns` and returns it at its exit. A worker
   contract that consumes authority (worker retirement) or produces it (worker
   establishment) is outside this protocol and stays refused.
4. **Members cross as ordinary resources.** `owns R(p)` in a worker contract
   lends a member to the worker, and join returns it. `consumes R(p)` without
   matching authority is not a spend. Join returns lent members with no
   change in the total.
5. **No relinquishment and no deferred spend.** A worker that lacks authority
   cannot end holding a member that it does not return. Sequential authority
   mode already refuses such a helper: its contract needs conserved `owns`
   resources or a checked `consumes`/`produces` effect. Join never creates
   or spends a member on a worker's behalf.
6. **Creation suspends the parent's use of transferred resources.** A
   successful create moves the task resources, including any authority and
   members, to the child. Until the matching join, the parent cannot observe
   that population, create or spend its members, retire it, or free its
   anchor, because each of those needs the authority it no longer owns. A
   failed create leaves every task resource with the parent, unchanged, as the
   [modeled pthread specification](https://github.com/clicklang/click/blob/master/src/languages/c/modeled_pthread_spec.md)
   already states.
7. **The worker's proof starts from an opaque total.** A worker that receives
   authority starts its standalone proof like a verified sequential helper
   that borrows raw authority. Its entry total is opaque, bounded below by the
   members it owns on entry. It has no creator right, so it cannot establish
   the population. Only a checked control invariant that the worker owns
   supplies a relation between the total and C state.
8. **Join returns the authority with the worker's checked delta.** Join
   consumes the completion right and returns the child's authority and
   produced members. The parent's ledger then applies the child's checked
   member delta, just as a sequential call return does. Every current
   observation after join is fresh. Facts from before the create, including
   `old(count(...))`, are historical. Join does not authorize any transition:
   the worker performed each one while it owned the authority.
9. **Scopes stay disjoint.** A wildcard observation `count(R(q, _))` needs the
   wildcard authority `authority(R(q, _))`. An exact authority, wherever it
   is held, does not grant a wildcard observation. Independent populations
   cross thread boundaries independently.
10. **Lifetimes are transported, not recreated.** Registration belongs to the
    anchor's storage lifetime. Create and join move that registration's
    authority; they do not mint a new identity, so a worker cannot establish a
    population for storage it did not create. Retiring the authority needs
    the authority, and freeing the anchor needs every authority retired.
    Together these rules prevent reclamation while any worker holds the
    authority or a member it must return.

## Shared populations without a lock

Because authority is exclusive, at most one outstanding worker holds the
authority of a given population. Any other concurrent worker of that
population may only borrow members. Its members come back at join, and the
authority holder spends them afterward. This is the specifically justified
deferred transfer that the issue allows: ownership of the member is deferred
until join, while the change in the count is not deferred. No count changes
outside the authority holder, and join performs no population update.

The legacy fixtures let two lock-free workers each consume a member of one
population and committed both consumptions at join. That is the retroactive
authorization the issue forbids, and the new model does not keep it. Workers
that must change a shared population concurrently use a mutex-held control
(milestone 4), so each update happens while its worker owns the authority.

## Compatibility with ownership held elsewhere

The protocol introduces no transition beyond the sequential ones. Its
soundness argument is the sequential one plus the exclusivity of each
transferred resource:

- Create and join are ownership transfers. They add nothing to the combined
  ownership of parent and child, so they preserve every outstanding fragment.
- While a worker owns the authority, the parent owns none and cannot make a
  population transition. The worker's transitions are the sequential checked
  `fold`/`unfold` exchanges, which are frame-preserving against members owned
  elsewhere because they create or consume only members that the worker owns.
- A worker without authority holds only members. Members do not expose the
  total or any shared accounting state, so the parent's exact observations
  stay valid while members are lent out.
- Exact totals remain justified by the creation ledger: the ledger counts
  every birth and spend, and every one of those happens under the single
  authority. Final zero needs the same retirement check as sequential code.

In the terms of the
[authoritative construction](https://plv.mpi-sws.org/coqdoc/iris/iris.algebra.auth.html),
fragment holders cannot change the authoritative total. They return fragments
to the authoritative holder instead. Similar terminology implies no Iris
embedding or inherited soundness.

## Constraints on milestone 4

The lock-based shared refcount of milestone 6 chunk 4 reaches authority through
a mutex. Milestone 4 must therefore provide these properties:

- A control deposited at checked initialization may own `authority(R(p))`.
  While it is deposited, its registration and ledger stay live and belong to
  the escrow. No thread observes or changes the population until it acquires
  the control.
- Lock returns the control as an ordinary owned resource. Its count
  observations are fresh, constrained only by the control's facts and the
  members the acquiring thread owns. Unlock requires the control folded with
  its facts true at the current ledger.
- A worker that holds only a `mutex_use` share and members can acquire the
  control. Worker task resources never include a control that sits in escrow.
- Destroy returns the control, with its authority, to the caller after every
  `mutex_use` share has returned. Retirement and anchor reclamation happen
  only after that.
- The escrow treats the control as an ordinary exclusive resource. No rule in
  the mutex path refers to counted populations.

## Fixture mapping

Each legacy worker fixture keeps its C unchanged. Replacements that spend a
member declare an ordinary field-free resource, `resource ticket(p: void*) {}`,
instead of `abstract resource ticket(p: void*);`. Authority mode has no checked
spend for abstract members: it refuses `unfold` of an abstract member because
its members require an ordinary producing contract. A worker that spends
carries `owns authority(ticket(argument))` and unfolds its member. A worker
that borrows carries only `owns ticket(argument)`.

Abstract workers and joins (milestone 6 chunk 2):

| Fixture | Legacy | Replacement under this protocol |
| --- | --- | --- |
| `modeled_pthread_counted_join.md` | pass | Pass. The worker owns the authority and spends its member; the parent observes zero after join. |
| `modeled_pthread_counted_reverse_join.md` | pass | Pass. Each worker owns the authority of its own population; both join orders observe fresh totals. |
| `modeled_pthread_counted_before_join.md` | fail | Fail. The parent's observation between create and join lacks the authority lent to the worker. |
| `modeled_pthread_counted_join_stale.md` | fail | Fail. After join, the fresh total is zero, so the stale `count == 1` is false. |
| `modeled_pthread_counted_neutral_pending.md` | fail | Split; see [outcome changes](#outcome-changes). A borrowing worker leaves the authority with the parent, which observes the exact total before join. A worker that borrows the authority neutrally still blocks the parent's observation. |
| `modeled_pthread_counted_pending_helper.md` | fail | Fail. The helper's count precondition needs authority, which the caller has lent to the worker. |
| `modeled_pthread_counted_pending_wildcard.md` | fail | Fail. A wildcard count needs the wildcard authority, which the parent does not own; the lent exact authority does not supply it. |
| `modeled_pthread_counted_overlap_rejected.md` | fail | Fail. A worker that observes the count needs the authority, so a second worker of the same population cannot also hold it. |
| `modeled_pthread_thread_confined_resource_rejected.md` | fail | Replaced; see [outcome changes](#outcome-changes). Its member-body counter invariant is a legacy-only shape. |

Shared abstract worker population (milestone 6 chunk 3). In each positive
replacement, both workers borrow members, and the parent spends each returned
member after the join that returns it:

| Fixture | Legacy | Replacement under this protocol |
| --- | --- | --- |
| `modeled_pthread_counted_shared_join.md` | pass | Pass in reverse join order; the parent spends after each join and observes fresh totals. |
| `modeled_pthread_counted_shared_forward_join.md` | pass | Pass in forward join order. |
| `modeled_pthread_counted_shared_partial_then_create.md` | pass | Pass. A returned member is spent before the reused handle creates a third worker. |
| `modeled_pthread_counted_shared_retained.md` | pass | Pass. The parent's retained member keeps the final total at one. |
| `modeled_pthread_counted_shared_symbolic.md` | pass | Pass with an opaque entry total `n >= 2`; the final total is `n - 2`. |
| `modeled_pthread_counted_shared_neutral.md` | pass | Pass. Nothing is spent; the total stays two. |
| `modeled_pthread_counted_shared_observer.md` | fail | Fail. The observing worker needs the authority, which a borrowing worker cannot share. |
| `modeled_pthread_counted_shared_stale.md` | fail | Fail. After both spends, the stale `count == 2` is false. |
| `modeled_pthread_counted_shared_early_count.md` | fail | Fail. The first worker's member is still lent, so the parent cannot spend it, and the total cannot reach zero before that join. |
| `modeled_pthread_counted_shared_missing_unit.md` | fail | Fail. The second create needs a member the parent does not own. |

## Outcome changes

Three behaviors change. Each change follows from the authority rule, and a
negative fixture keeps the refusal it protected:

- **Count refusals while a worker is outstanding.** Legacy refused any parent
  count observation while a worker that mentioned the population was
  outstanding. The new refusal is narrower and explicit: an observation needs
  the authority, so it fails exactly when the authority is lent. The diagnostic
  must name the missing authority and the worker that holds it, in place of
  `count(...) requires joining its outstanding worker`.
- **`modeled_pthread_counted_neutral_pending.md`.** Its worker borrows only a
  member, so under this protocol the parent keeps the authority and may observe
  the exact total before join. That observation is sound because the borrowing
  worker cannot change the total. Migration adds this positive and keeps the
  refusal as a negative in which the neutral worker also borrows the authority.
- **`modeled_pthread_thread_confined_resource_rejected.md`.** Its member body
  owns the counter and states a count fact, a shape that authority mode does
  not admit. Under authority, a member is no longer thread-confined: lending it
  to a worker is an ordinary transfer. The replacement keeps the protected
  property, that a member alone cannot expose shared accounting, with
  negatives in which a worker that borrows only the member observes the count
  or accesses the counter, and both fail.

## Implementation

Authority-mode create applies the worker's verified contract exactly as the
entry and body of a sequential call do: the checked partition moves the task
resources, including any `owns authority(R(p))`, to the worker's call identity
in the creation ledger, and the contract's checked member effects apply under
that identity. The parent then continues with that ledger but without the
worker's resources, so it holds neither the lent authority nor the lent
members. A failed create selects the parent's unchanged ledger. Join performs
the sequential return: the worker's outputs move back to the parent through
the same ledger transfer, and the call must retain nothing. Join itself makes
no population transition, and every count observed afterward is read from the
ledger. A count whose authority is lent reports `count(...) requires owning
authority for that population, which an outstanding worker holds until its
pthread_join`. The contract-claims recheck replays both transitions, and
`click audit` expands and reverifies the migrated fixtures.

A worker contract is admitted by the sequential authority-mode rules, so a
worker that consumes or produces authority, or keeps a member it cannot
spend, is refused at create or in its own proof.

## Implementation chunks

Milestone 6 chunk 2 implements this protocol for authority-mode
`pthread_create` and `pthread_join`. It suspends the parent's use of the
transferred authority, applies the worker's checked delta at join, and adds
independent certificate checks for both transitions. Misuse regressions cover:

- observing, retiring, or freeing while a worker holds the authority;
- a worker that relinquishes a member;
- a worker that consumes or produces the authority; and
- reusing a pre-create observation after join.

Chunk 3 migrates the shared fixtures with no further capability. If either
chunk finds that the protocol needs more than these existing transfers, that is
a design change to discuss before coding, not an implementation detail.
