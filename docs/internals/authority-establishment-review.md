# Object-anchored population authority

This records the selected lifetime protocol for the authority migration.
See `issues/authority-migration.md` for rollout order and the
[consumer inventory](authority-migration-inventory.md) for existing clients.
The new abstract kernel model is additive; existing projects still use legacy
counting. An authority-mode project can be selected with
`{"resource_semantics":"authority"}` in `click.project.json`. Its restricted
source slice admits an exact unary population established in the storage
creator's execution proof. A field-free resource with a private owned-memory
body can be folded to create one member and unfolded to consume it while
matching authority is owned. Opening an existing member temporarily exposes
its body without changing membership. Current `count(R(p))` reads the checked
total only with that authority. Retirement requires zero members. Verified
ordinary C helpers may borrow and return the same exact authority and member;
their standalone proofs receive an opaque population with no known count or
creator right. An imported member can be opened to use its private owned-memory
body, then closed before return. The helper does not need a concrete caller
allocation in its standalone proof; the caller established the member against
live storage before transferring it. Other contract transitions, worker calls,
recorded-state count, and field-bearing or nested member bodies remain refused.

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

The C bridge preserves this registration through ordinary verified helpers
that return the same borrowed authority and member. Wrappers, frames, and
thread transfers still need checked integration.
Minting a fresh internal identifier whenever a pointer is encountered would
violate this rule. The abstract kernel allocator
creates fresh abstract lifetimes only; it grants no C memory permission and is
not a source-level authority constructor.

Establishment must also precede any member creation for that population. The
creation environment alone does not prove emptiness at an arbitrary later
point: it might already have produced and transferred ordinary `reference(p)`
instances. The source slice checks production and consumption of one field-free
member with a private owned-memory body at a time, exchanging that body and the
owned member fact while changing the exact total in one certificate event. Its
creation ledger retains per-family member history, so local absence
after consumption or future transfer cannot justify re-establishment. Other
member forms still require checked integration.

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
lifetime and may establish its own authority. The anchor cannot be freed while
any authority remains registered. Scope exit cannot silently discard authority, members, or anchor
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
existing tactic syntax and record a dedicated checked certificate event. In
the initial source slice, ordinary wrapper folding is refused until its
member and authority exchange is checked.

The additive kernel model exercises ownership, registration, membership,
transfer, retirement, and cleanup with concrete totals. It does not yet admit
C bindings, symbolic totals, wildcard scopes, views, or loans. Those must be
implemented explicitly, including nonoverlap checks for population scopes;
independent authorities must never count overlapping sets of members.

Legacy proofs remain unchanged. The temporary migration boundary covers a
complete verification unit and is included in proof/cache identity. New proofs
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
restrictions. A separate C event ledger records successful heap creation and
actual automatic declarations, uses distinct caller/callee environments, and
clears provenance on direct free, scope exit, and checked contract retirement.
It retains per-storage family history: once a member existed, transferring it
away cannot make later establishment appear empty. Pending heap outcomes carry
that history to the resolved allocation. The first query accepts an exact heap
or automatic-object base; subobject/interior anchors still need checked
canonicalization. Its opt-in is enabled only by an authority-mode source proof
or kernel test. Resource transitions must be connected to this history before
source member operations can use it.

The source parser recognizes `authority(R(p))` for an exact unary, field-free,
pointer-anchored declared family, and lowers it to a distinct exclusive kernel
resource. Ordinary resource evaluation refuses to mint it. The explicit
project mode and proof artifacts carry the semantics choice. Checked source
`fold`/`unfold` establish and retire authority; direct `fold(R(p))` and
`unfold(R(p))` create and consume one field-free member, exchanging its private
owned-memory body. The exchange requires matching owned authority and is
rechecked by the certificate checker. `open(R(p))` exposes that body while
preserving membership, and its close restores the body. Current exact
`count(R(p))` reads the ledger, never the legacy population state. A verified
ordinary helper can borrow and return the same authority and member through
the checked resource contract and creation ledger. Its standalone proof imports
only that declared custody as an opaque population: it cannot observe a total,
create or consume members, or retire authority. Other contract transitions,
worker calls, field-bearing or nested member bodies, and historical count
observations still need integration before authority mode can verify a real
counted-resource program.
