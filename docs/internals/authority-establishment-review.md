# Object-anchored population authority

This records the selected lifetime protocol for the authority migration.
See `issues/authority-migration.md` for rollout order and the
[consumer inventory](authority-migration-inventory.md) for existing clients.
The new abstract kernel model is additive; current C proofs still use legacy
counting. No new source operation is implemented by this checkpoint.

## Establishment and uniqueness

A population is anchored to the lifetime of a C object appearing as an argument
of its resource type. The initial slice is exact unary `reference(p)`.
Authority may be established only in the execution environment that actually
creates the storage, while that environment owns the anchor. Each population
scope may be established once during that storage lifetime. Establishment
creates an empty population; creating its first member is a separate checked
transition. Receiving ownership of existing storage does not grant permission
to establish authority, even when its population has never been registered.

Registration belongs to the anchor lifetime, not to the current local proof
context. Passing the anchor to another owner preserves its registrations even
when the authority remains with the original owner. Neither local absence of
members nor recovery of raw memory ownership permits duplicate establishment.
Aliases must resolve to the same anchor lifetime and registration. Reuse of a
C address after deallocation must resolve to a new lifetime.

The checked C bridge must preserve this registration through calls, wrappers,
frames, and thread transfers. Minting a fresh internal identifier whenever a
pointer is encountered would violate this rule. The abstract kernel allocator
creates fresh abstract lifetimes only; it grants no C memory permission and is
not a source-level authority constructor.

Establishment must also precede any member creation for that population. The
creation environment alone does not prove emptiness at an arbitrary later
point: it might already have produced and transferred ordinary `reference(p)`
instances. Before exposing source establishment, the bridge must retain a
pristine-population check across these transitions and escapes. Local absence
of members is insufficient. The abstract model currently only admits member
creation under existing authority; ordinary-resource enrollment remains a
separate integration obligation.

## Membership and cleanup

Only the authority holder may observe the exact total, create members, or
consume members. Consumption additionally requires owning the members being
consumed. Transferring members needs their ownership but does not need authority
and does not change the total. Authority can be transferred independently of
members and anchor ownership.

Retirement requires authority and a zero total. It removes the live authority
but retains the fact that this scope has already been established until the
anchor lifetime ends. Re-establishment during the same lifetime is forbidden,
including in the original creating environment. Outstanding members prevent
retirement. A new actual allocation, even at the same address, has a new
lifetime and may establish its own authority. The anchor cannot be freed while any authority remains
registered. Scope exit cannot silently discard authority, members, or anchor
ownership. Moving these obligations to another owner is allowed.

A closed control resource packages authority along with its counter ownership
and invariant. Opening that ordinary resource exposes the permissions needed
to change membership and counter together; closing must reestablish its facts.
The standalone kernel model does not yet implement this wrapper integration.

## Syntax and staged implementation

The intended resource expression remains `authority(reference(p))`, composed
using ordinary `owns`, `consumes`, and `produces`. No new keyword is selected.
The existing `construct` operation creates abstract tokens under an outcome
contract; it does not establish the lifetime or registration evidence above.
The proposed reuse of `construct` has not been adopted. The selected source
operations are `fold(authority(reference(p)))` for empty establishment and
`unfold(authority(reference(p)))` for zero-count retirement. These reuse the
existing tactic syntax; their new checked resource behavior is not yet wired
to source proofs. Ordinary wrapper folding requires already-owned authority
and cannot bypass the establishment checks.

The additive kernel model exercises ownership, registration, membership,
transfer, retirement, and cleanup with concrete totals. It does not yet admit
C bindings, symbolic totals, wildcard scopes, views, or loans. Those must be
implemented explicitly, including nonoverlap checks for population scopes;
independent authorities must never count overlapping sets of members.

Legacy proofs remain unchanged until the C bridge and source interface have
positive and negative fixtures. The temporary migration boundary must cover a
complete verification unit and be included in proof/cache identity. New proofs
must not fall back to legacy counting. Existing examples migrate in the order
recorded in the issue before legacy semantics and `guarded_by` are removed.

## C creation events and explicit helper contracts

For heap storage, the creation event is successful resolution of an actual
`malloc` (also `calloc` and `realloc(NULL, size)`); allocation failure grants
nothing. The originating invocation is recorded when allocation is initiated:
a helper that merely tests the pending result cannot become its creator.
Successful resolution uses that recorded origin even across a call.
Successful reallocation of existing storage ends its old lifetime,
so it must first satisfy the same authority-retirement obligations as free.
The initial bridge must withhold establishment permission for that case until
its checked retirement/creation transition is implemented. For automatic storage, it is the
execution of the object's declaration. A copied pointer is an alias, not a new
object. Re-entering a declaration after its prior lifetime ends creates a new
lifetime. Global storage needs a startup proof environment before it can use
this rule; ordinary function entry must not re-create global authority.

The creator establishes empty authority before calling an initializer. The
initializer receives that authority explicitly through its ordinary resource
contract and uses it to create the first member. A helper that receives only
memory or `allocation(p, size)` cannot establish authority. The earlier
allocation-custody proposal is superseded; authority need not retain the heap
allocation resource, and this design does not restrict anchors to heap objects.

For example, the intended initializer interface uses existing contract clauses
(the authority resource itself is still being implemented):

```text
void object_init(struct object* p) {
    consumes allocation(p, sizeof(struct object));
    consumes object(p);
    consumes authority(reference(p));
    requires count(reference(p)) == 0;
    produces control(p);
    produces reference(p);
}
```

Here `control(p)` packages the allocation, memory, authority, and counter
invariant. Its allocation ownership serves ordinary eventual deallocation;
it does not justify establishing authority. The caller must obtain authority
at the creation site before invoking this helper. The original C need not
change. The creator uses the checked authority `fold` operation before the call.

The concrete bridge points are successful `resolve_pending_heap_allocations`
and real `declare_local` / `declare_aggregate_local` events in
`src/kernel/eval/statements.rs`. `with_heap_allocation_claim` in
`src/kernel/primitives/memory_state.rs` imports a claim about existing storage
and grants no creation permission. Generic `with_block` is also insufficient:
it creates verifier-generated parameter slots and other synthetic storage.

A distinct invocation identity must distinguish caller and callee, even if
neither needs address-backed parameter slots. Existing `next_local_frame` is
not such an identity. Calls preserve population registration and transport
explicit authority, while retaining unspent creation permission in its
originating environment. Returns restore the caller's environment. Direct
free, scope exit, and contract retirement must reject live authorities before
ending the anchor lifetime.

The abstract kernel checks the creation-environment and once-per-lifetime
restrictions. A separate C event ledger now records successful heap creation,
uses distinct caller/callee environments, and clears provenance on direct free
and checked contract retirement. The first query accepts an exact heap base;
subobject/interior anchors still need checked canonicalization. Its opt-in is internal to kernel tests; it
neither creates authority nor changes existing source verification. Stack
creation, authority transfer through contracts, the pristine-population check,
and source `fold`/`unfold` behavior remain to be implemented. Tests of C event
provenance do not yet prove those authority integration boundaries.
