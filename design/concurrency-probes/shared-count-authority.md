# Shared counter accounting: next language boundary

Status: shelved proposal, not implemented syntax or verified code. First test
the ordinary-resource approach; this document is not an implementation plan. The
unchanged counter already verifies for safety. Its exact final value requires
shared accounting that the current sequential population mechanism cannot
supply.

## Ordinary-resource experiment

Existing syntax can express a bundle of credits:

```click
abstract resource increment_credit(p: struct mutex_counter*);
resource credits(p: struct mutex_counter*) {
    field amount: int32;
    owns amount of increment_credit(p);
}
```

A scalar model field can supply the quantity. Folding consumes the actual
credits and checks nonnegativity; unfolding an owned bundle recovers them.
Flat ordinary tokens, including symbolic quantities, can also be ingredients
of the mutex-protected resource. They add no memory footprint.

The regressions `resource_model_quantity.md` and
`mutex_use_preserves_resource_quantity.md` exercise these existing operations.
No count-authority primitive or new surface notation is involved.

The attempted deposit invariant relates the C counter to the number of
protected credits and bounds both by two. A worker consumes one external
credit and deposits it while incrementing. It reaches the obligation
`credits + 1 <= 2`, which does not follow from `credits <= 2` and ownership of
one external credit. That contract allows two credits inside and another
outside. `mutex_resource_quantity_requires_conservation.md` preserves this
expected failure against the unchanged C.

Abstract credits also need an initial source: verified code cannot freely
mint them. Assuming two credits from a caller is a useful experiment, but
does not discharge the original parent's memory-only precondition. These
are the remaining conservation and initialization questions. This experiment
does not establish that the interface proposed below is necessary; it remains
shelved pending a smaller ordinary-resource solution.

## Proposed resource interface

Keep ordinary worker contracts:

```text
consumes pending(p);
produces completed(p);
owns access: mutex_use(&p->mutex, counter_state(p));
```

Introduce one built-in resource type, `count_authority(R)`, where `R` is a
resource type such as `completed(p)`. It owns the authoritative population
state. An ordinary `completed(p)` unit is a fragment of that population.
Passing either type as an argument grants no ownership. The initial primitive
would support only bodyless resource families. Extending it to existing
populations with shared bodies or allocation obligations is a separate design
step.

The protected assertion would own the authorities explicitly:

```text
resource counter_state(p: struct mutex_counter*) {
    field value: uint32;
    guarded_by p->mutex;
    owns p->value;
    owns count_authority(pending(p));
    owns count_authority(completed(p));
    fact p->value == value;
    fact value == count(completed(p));
    fact count(pending(p)) <= 2;
    fact count(completed(p)) <= 2;
    fact count(pending(p)) + count(completed(p)) == 2;
}
```

The individual bounds make the conservation equality unambiguous under the
current bounded count arithmetic. Do not silently treat a wrapping addition
as mathematical addition.

A Count expression observes authority; it does not create it. In particular,
adding a fact mentioning `count(R)` must not give a second invariant another
copy of R's authority. Keeping authority in `owns` makes this visible in the
same resource interface as memory and guards.

## Creation is a separate operation

An authoritative state must exist even at total zero. It cannot be obtained
by unfolding a positive unit, or by assuming an arbitrary entry total is zero.
It also cannot be silently manufactured by ordinary `fold`, whose existing
meaning is to package resources already owned.

Proposed proof operation (name and surface form require review):

```text
let pending_total = create_count(pending(p));
let completed_total = create_count(completed(p));
```

Each operation creates a fresh population identity, an owned authority, and
an initial total of zero. This is ghost allocation, not a claim that every
population with the same printed resource arguments has total zero.
Authority and fragments retain the fresh identity through contracts, mutex
escrow, and worker transfer. Distinct generations cannot be combined even
when their resource types print identically. The initial slice should reject
ambiguous same-type population selection rather than guess an identity.
Contract instantiation must authenticate the worker's fragments against the
population identities owned by the selected mutex assertion.

Generation selection across modular contracts remains an unresolved checking
rule. The illustrative creation names above are not passed explicitly in later
`pending(p)` or `count(pending(p))` expressions. The checker must connect the
worker input, the mutex-owned authority, and the produced completed unit to
the same generations; freshness and ambiguity rejection alone do not prove
that connection. The proposed default is unique contextual selection through
the typed mutex assertion, with an independently checked contract relationship.

These identity requirements must be settled and implemented before this constructor is
exposed. Existing `count(R)` keys alone are insufficient. If unique contextual
selection proves inadequate, explicit population references would need a
separate surface review; do not introduce them speculatively.

## Updates and retirement

With the appropriate authority owned, use ordinary `fold(R)` and `unfold(R)`
to create and consume membership units, updating the total at that proof step.
This is a new checked interpretation for authority-backed populations, not a
change that permits arbitrary abstract-resource minting. Without authority,
fragments may be transferred but not created or destroyed. Fragment ownership
implies a lower bound on the total, never exact equality with the local quantity.

Initialization creates two pending units and zero completed units, then folds
the state and deposits both authorities in the mutex. The parent retains the
pending units and gives one to each successful worker. A failed creation
leaves its pending unit with the parent.

The worker acquires the authorities by locking and unfolding the protected
state. It executes the existing C increment, consumes one pending unit, creates
one completed unit, and restores the invariant before unlock. Its
`consumes`/`produces` clauses check this net change; function return must not
apply the change a second time.

Join returns only the child's completed unit. After both joins and destruction,
the parent owns both authorities and two completed units. The fragment lower
bound and invariant upper bound give total two, hence `p->value == 2`.
Failure paths recover the authorities after joining any started worker and
consume the pending and completed units actually present.

Authority retirement needs a checked operation requiring total zero and no
outstanding fragments or borrows. Its surface name is part of the same review
as creation. Merely dropping the authority must not let a later initialization
reuse an outstanding fragment's identity.

## Implementation obligations

- Add persistent authoritative population identities and indexed fragment
  support, including zero totals and exact retirement checks.
- Retain authority identity and conservation laws through mutex escrow while
  freshening observations. The current childless scalar payload rule must be
  extended to transport these owned resource ingredients.
- Mint abstract modular authority/fragment relationships from the contract,
  and authenticate those relationships at the call boundary.
- Record explicit checked population update deltas. Check return contracts
  against those deltas without double-applying their effect.
- Keep shared counts out of sequential snapshot-copying paths. Creation and
  join must not install a worker's saved global count state.
- Reject new exact observations of the current total without authority,
  mismatched population generations,
  duplicate authority, fragment minting without authority, missing/wrong
  increment, double completion, early retirement, and transport of old Count facts into
  current-state equalities. Historical snapshot equalities remain valid.
- Verify the unchanged C, creation-failure cleanup, reverse join order,
  deterministic scaling, expansion/reverification, and the full gate.

The alternative of deriving authority implicitly from `count(...)` would
hide the central ownership condition in a pure-looking expression. The
explicit built-in resource is preferable. No angle parameters or new
language keyword are needed; a resource primitive and ghost lifecycle
operations are genuine additions and should be reviewed as such.
