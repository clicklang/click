# Object-anchored population authority

This records the selected lifetime protocol for the authority migration.
See `issues/authority-migration.md` for rollout order and the
[consumer inventory](authority-migration-inventory.md) for existing clients.
The new abstract kernel model is additive; current C proofs still use legacy
counting. No new source operation is implemented by this checkpoint.

## Establishment and uniqueness

A population is anchored to the lifetime of a C object appearing as an argument
of its resource type. The initial slice is exact unary `reference(p)`.
Establishing authority requires exclusive ownership of the anchor and an
unregistered population scope. It creates an empty population. Creating its
first member is a separate authority-checked transition.

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

## Membership and cleanup

Only the authority holder may observe the exact total, create members, or
consume members. Consumption additionally requires owning the members being
consumed. Transferring members needs their ownership but does not need authority
and does not change the total. Authority can be transferred independently of
members and anchor ownership.

Retirement requires authority and a zero total. It removes the registration;
subsequent establishment receives a new population identity. Outstanding
members therefore prevent retirement and prevent replacement with a false
zero-count authority. The anchor cannot be freed while any authority remains
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
The proposed reuse of `construct` has not been adopted.

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

## C bridge decision still under review

A modular initializer receiving object memory cannot infer that the caller has
no authority elsewhere. The first proposed heap bridge consumes the existing
`allocation(p, size)` resource into authority custody and returns it only on
empty retirement. Object fields remain separately owned. This fits the current
refcount initializer without another contract term, but is not yet selected
or implemented. Stack/global and caller-owned pool objects need their own
checked lifetime permission; heap custody alone does not solve those cases.

Before using allocation as that witness, the new mode must enforce its
exclusivity. Today `own_allocation` constructs a token, and the token algebra
can combine equal owned tokens into quantities. Duplicate memory ownership
is rejected independently; an allocation token alone is not yet the unique
lifetime capability this bridge would require. Required regressions include
duplicate plain clauses, aliasing allocation claims, and transport through
composites and calls. This observation identifies a migration prerequisite;
it is not an established proof of a false C claim under current semantics.

The bridge audit points are `src/kernel/primitives/resource_algebra.rs`
(allocation construction, token algebra, context validity),
`src/kernel/primitives/memory_state.rs` (`with_heap_allocation_claim`), and
`src/kernel/eval/statements.rs` (malloc results and allocation retirement).
An allocation contract claim can describe existing storage; only an actual
fresh-allocation transition supplies fresh lifetime evidence.
