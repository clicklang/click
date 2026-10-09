# Modeled pthread create/join, mutex, and publication specification, version 11

This trusted specification is an explicit assumption of a conditional Click
client proof. It does not certify an operating system's pthread implementation.

- `pthread_create` evaluates its arguments once. With null attributes and a
  direct verified, terminating worker, a zero result creates one joinable child,
  transfers the worker's checked task resources, and stores a handle in the
  caller's authorized output slot. A nonzero result creates no child and leaves
  those task resources with the caller. The output slot is unspecified on
  failure. The parent cannot use the worker's returned resources or
  postconditions before a checked join.
- `pthread_join` accepts a live handle for this parent's unique joinable child
  with exact termination evidence, no detach, cancellation, competing join, or
  self-join. Under those preconditions the runtime join succeeds, consumes the
  one completion right, and makes that child's checked output delta and
  postconditions available. The initial binding requires a null result slot.
- Handles are C values associated with an unforgeable creation identity.
  Copies preserve that identity but never duplicate its completion right.
  Integer representations alone grant no thread authority.
- `pthread_mutex_init` with null attributes and a selected folded, exclusive
  resource succeeds and deposits that resource in the mutex; initialization
  is what associates the resource with this mutex. This model treats the mutex bytes as
  opaque and creates one exclusive `mutex_live` resource for this initialization.
  Initialization without a selected protected resource creates that owner too.
  Both forms require the complete 40-byte writable storage and 8-byte alignment.
  Local automatic objects provide implicit ownership within their live bounds;
  other storage requires an ordinary owned memory range. A stable view cannot
  authorize initialization, and an active storage loan prevents it. Initialization
  forgets previous values of the mutex bytes while preserving disjoint memory.
- `pthread_mutex_lock` requires the current initialization's available
  `mutex_live` owner or a checked owned `mutex_use` loan for that initialization.
  It succeeds for an unlocked mutex and gives
  the current path its escrowed resource. `pthread_mutex_unlock` succeeds only
  when an owned instance of the authenticated protected resource type has been
  folded and returned to escrow.
  `pthread_mutex_destroy` succeeds only for an unlocked initialized mutex,
  consumes its `mutex_live` owner, and returns its protected resource to the caller. These calls do not branch on a failure
  status under their checked preconditions.

The owner is separate from the guard: it implies neither heldness nor payload
access. Describing an initialized address grants no ownership. Folded owners
must be unfolded before lock or destroy; an old initialization's owner cannot
authorize either transition after reinitialization at the same address.

Typed worker inputs `owns access: mutex_use(mu, counter_state(p))` receive a
checked share of use authority. Creation lends the lifetime owner on the first
use, retains a parent share, and splits a separate worker share on each success.
Failure leaves the parent's authority unchanged. Join returns only that child's
share into the current loan ledger. Destruction requires every share to return;
a saved pre-create state cannot replace the current state. Creation while the
parent holds a guard remains outside this profile.

Protected observations are fresh at worker acquisition and at concrete summary
calls. While workers remain, parent acquisition and release forget protected
observations consistently with the resource definition. This admits arbitrary
worker interference between critical sections without transferring the payload
to an unlocked parent. Shared worker effects currently require external storage.
The exact final value requires additional contribution accounting.
The current modeled ABI gives each mutex a 40-byte storage footprint. An
allocation overlapping any initialized footprint cannot be freed, reallocated,
or retired by a helper contract until the mutex is destroyed. Lock/unlock do
not release this dependency. Distinct storage can still be released. Abstract
preserving-guard contracts cannot yet retire allocations because their
lifetime dependencies are not represented by checked lifecycle inputs.

Functions cannot return with held guards or escrowed protected resources unless
a preserving guard contract carries them. An unlocked empty mutex currently
has no general return obligation. Automatic storage, however, cannot expire
while it contains any initialized mutex: the mutex must be destroyed before
normal or abrupt scope exit, including function return. Folding its owner into
a resource does not remove this storage dependency. Unresolved symbolic mutex
storage conservatively blocks expiry when it might alias the local object.
Initialization now checks storage ownership, known lifetime expiry, read-only
storage, alignment, and stable loans. Successful initialization reserves its
footprint against ordinary C stores, aggregate writes, call-result assignments,
and modular calls whose mutable footprint may overlap it. Another initialization
must also be separate. Unlocking or folding lifecycle ownership does not release
the reservation; destruction does. Missing separation reports `Requires separate(...)`.
Every checked mutex runtime transition may change its opaque bytes, forgets their
old values, and must respect active stable storage loans.

Reservations are retained in the concrete runtime ledger. Independently verified
preserving helpers also retain the storage dependencies of their assumed owned
mutex inputs, including inputs inside declared resources. These dependencies
survive changes to the visible resource representation, do not grant runtime
authority. Unknown dependencies are conservative. Direct preserving `mutex_use`
helpers may perform balanced opaque lock/unlock: acquisition creates an exact
local guard and lifetime hold, and release consumes both. These operations
expose no protected assertion. Return requires the preserved use input with no
outstanding acquisition or child loan. Init/destroy and
escaping acquisitions remain unsupported in this abstract path. Typed use inputs
add an authenticated protected resource type: lock produces `guard` and `state`,
and unlock consumes the guard and an owned replacement of that resource type.

Every synchronous use contract currently permits balanced acquisition. Calls
therefore conservatively require the selected concrete initialization to be
unlocked and reject potentially aliased owned abstract guards, including guards
hidden in entry wrappers. This is local availability, not a promise of global
unlockedness, fairness, or termination. Such calls may change the opaque mutex
representation: their checked summaries forget those storage bytes and respect
stable storage loans, even when the caller retains ordinary storage ownership.

The C client still owes its worker proof, creation failure paths, ownership
separation, parent access checks, and every source-level continuation. The
current checked C transition supports one unresolved creation at a time,
scalar local work and an owner-authorized store to disjoint external memory
before its status test, and a checked join after the status selects success.
Other intervening operations and additional pending creates are refused until
their guarded authority can be represented and checked.

The runtime declares the mutex operation binder schemas centrally. The current
named projection consumes initialization's `state` and produces `lifetime`:
`let { lifetime: life } = step(pthread_mutex_init(mu, 0), { state: instance })`.
Destruction accepts `step(pthread_mutex_destroy(mu), { lifetime: life })`.
The ordinary call-map checker validates these declarations, including missing,
unknown, and duplicate binders. The kernel independently validates the selected
binder identities and owned resources. A lifecycle name denotes the exact
initialization, not merely its address; destruction and reinitialization cannot
revive an old name. Named preserving lifecycle and guard helper contracts use
the same call maps and preserve their selected authority through checked
occurrence transfers. Typed-use lock and unlock accept the named `access`, `guard`, and `state`
binders. A suspended worker's input name is local to its contract; create selects
and checks the required authority without adding a proof argument to the C call.

## One-shot release/acquire publication

The runtime also models one C11 protocol from Click's `<stdatomic.h>`
projection: one `atomic_int` flag that publishes one payload once. The
projection gives `atomic_int` the size and alignment of `int`; the operations
are declared with plain `int` arguments, and only Click's own declarations are
modeled.

- `atomic_init(&flag, 0)` takes `{ payload: P(args) }`, where `P` is a declared
  resource with a body and no fields. It requires 4 bytes of explicit, writable,
  4-byte-aligned storage at `flag` and the constant value 0, consumes that
  storage ownership, and mints `publisher(&flag, P(args))` and
  `subscriber(&flag, P(args))`. The storage stays consumed: C11 has no atomic
  destroy, so the flag is never again an ordinary object in this model.
- `atomic_store_explicit(&flag, v, memory_order_release)` requires a value
  proven nonzero, `publisher(&flag, P)`, and a folded owned `P`. It consumes
  both and forgets the values in `P`'s footprint, because the acquiring thread
  may change them from then on.
- `atomic_load_explicit(&flag, memory_order_acquire)` returns an
  unconstrained `int`. With `subscriber(&flag, P)` held, the right is marked as
  read through that value until a C branch decides whether it is zero. The
  branch that knows it is zero keeps the subscriber right. The branch that
  knows it is nonzero exchanges the right for `P`. A load without the right
  returns a value and transfers nothing. A load while an earlier read through
  the same right is still untested is refused.
- Any other memory order is refused, including `memory_order_seq_cst`.

The rights are affine and unique per flag and side. They are not
thread-confined, so a worker contract may consume either right. Dropping a
right is allowed. Ordinary loads and stores of the flag need the consumed
storage ownership, so they are refused.
