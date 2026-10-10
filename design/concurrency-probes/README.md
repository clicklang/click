# Concurrency profile and verified fork/join probe

This records the source selection and runtime boundary for the completed
concurrency demo; [broader concurrency](../../issues/concurrency-and-atomics.md)
remains open. The synthetic
[`fork_join.c`](../../examples/concurrency-fork-join/fork_join.c) is ordinary
C11/POSIX source fixed before its contracts and thread rules were written.
Its [Click sidecar](../../examples/concurrency-fork-join/fork_join.click) now
verifies both the worker and parent under the explicit modeled pthread runtime.
The normal example gate verifies that project, and the source-integrity test
in `tests/examples.rs` pins the C bytes.

The [mutex counter source](mutex_counter.c) is frozen separately. Its two
workers mutate the same ordinary cell under one lock. The
[shared-protocol design](mutex-shared-protocol.md) records the authority and
interference rules. The [sidecar](mutex_counter.click) verifies the unchanged
counter and its exact result: when both workers start and join, the counter
is two. The mutex protects a control that owns the counter and the authorities
for two populations, contributions already made and credits still to spend;
each worker spends a credit and creates a contribution while it holds the
lock, so the control's facts tie the counter to the contribution count.
`mdtests/mutex_counter_*_rejected.md` refuse a wrong increment, a fabricated
credit, a doubled contribution, and a total read before the second join. Both
earlier proposals, the
[counted-resource investigation](shared-count-authority.md) and the
[explicit-authority proposal](explicit-authority.md), are superseded by
population authority: a mutex protects an ordinary control that owns
`authority(...)`, as `examples/shared-refcount/` shows.

The unchanged [mutex parity source](mutex_held_parity.c) and its
[sidecar](mutex_held_parity.click) now verify under the modeled pthread
runtime for every `int32 n`, including negative values, zero, both final
parities, and the largest positive value. A conditional resource owns
`mutex_guard` when its `parity` field is one; the loop invariant relates that
field to `i % 2`. Each iteration returns the required ownership with a fresh
acquisition when appropriate. The final conditional unlock and destruction
verify as well. The normal example test gate checks the sidecar and pins the
original C bytes. The [direct sidecar](mutex_held_parity_direct.click) verifies
the same source using `if i % 2 == 1 { owns mutex_guard(&object->mutex); }`
in the loop contract. Both forms remain checked by the normal gate.

This first milestone covers an initialized empty mutex whose lifetime is owned
locally. It does not demonstrate shared-worker interference or protected
payload transfer. Conditional loop abstraction currently supports one direct
guard ingredient under a scalar model comparison. Nonempty mutex invariants,
use-loan-backed acquisitions, nested/matched guard wrappers, and joins of exits
with different mutex receipts remain outside this slice. Other mutexes retain
the strict protocol comparison; the loop cannot silently change their state.

Hostile regressions reject a false parity invariant and an unguarded unlock.
Kernel tests additionally reject missing or extra guard custody, stale
acquisitions, changed initialization, outstanding use loans, and changes to
framed mutexes. Deterministic scaling tests vary unrelated definitions,
resources, and mutexes. The next milestone is the shared-worker counter above;
after that proof, compare the implemented resource machinery with the design
and with the abstractions the two demonstrations actually needed.

## Binding direction

The [pthread binding design](pthread-binding-design.md) describes how ordinary
C create/join calls use the existing worker contracts, `step`, and `branch`.
The modeled-runtime identity and a first checked C create/join path now run on
macOS. One pending creation may survive scalar local work and an
owner-authorized store to disjoint external memory before a C branch chooses
success or failure. Two sequential creates over disjoint task cells now verify
all three parent outcomes, including the second failure's cleanup join and
both successful join orders. Source regressions reject abandoning the first
completion on second failure and reading a child's cell before its join. The
parent can now split one explicit stable view between two read-only workers;
their source proof covers both join orders and cleanup after a failed second
create. The same sharing now works for a parent stack cell without an
ownership annotation, and rejects writes or scope exit while a reader lives.
An explicitly owned cell can likewise back both readers; the owner returns
only after the final join, including when joins occur in reverse order.
The frozen parent has a complete sidecar proof. Broader guarded operations
remain future work.

## Selected profile

| Boundary | Selection |
| --- | --- |
| Language and target | C11, x86-64 Linux user space, LP64, eight-bit bytes and `-funsigned-char`. The example project selects `x86_64-linux-userspace` in `click.project.json`, which chooses the include model without `__KERNEL__` and a distinct proof-artifact identity. The same config explicitly selects `modeled-pthread`; target selection alone supplies no thread semantics. |
| C library interface | Click's built-in `<pthread.h>`, `<stddef.h>`, and `<stdatomic.h>`, with the [modeled pthread specification](../../src/languages/c/modeled_pthread_spec.md). Proofs hold for any C library that implements that interface; Click does not import or verify a platform's headers or runtime to supply it. |
| Compile options | `-std=c11 -pthread -funsigned-char -D_POSIX_C_SOURCE=200809L`. No optimizer- or scheduler-specific ordering assumption belongs in a proof. |
| Thread API | The selected `pthread.h` declarations for `pthread_create` and `pthread_join`, with joinable threads only. The declaration projection spells `pthread_t` as its x86-64 ABI `unsigned long`; checked modeled rules treat its value as a handle rather than deriving thread behavior from integer arithmetic. Spawn success creates exactly one child and a completion handle; failure creates none. A successful join consumes that handle exactly once. |
| Later mutex API | `pthread_mutex_init`, `pthread_mutex_lock`, `pthread_mutex_unlock`, and `pthread_mutex_destroy` on one ordinary POSIX mutex, with checked guard/resource transfer. No recursive mutex, condition variable, cancellation, detach, or signal operation. |
| Later atomic subset | C11 `_Atomic int` with `atomic_init`, `atomic_store_explicit(..., memory_order_release)`, and `atomic_load_explicit(..., memory_order_acquire)` for one-shot publication. No read-modify-write, fence, relaxed protocol, or implicit strengthening to sequential consistency. |

The first Click import is a declaration-only projection of `<pthread.h>` and
`<stddef.h>` sufficient to parse the frozen source unchanged. The separate
modeled runtime supplies checked create/join transitions under an explicit
assumption; the declarations themselves supply no pthread external contracts
or scheduler semantics. Only null attributes and null join-result arguments
are in the selected first probe. The frozen source is now a verified modeled
concurrency example.

The pthread implementation is a trusted runtime boundary, not a verified C
body. Its specification identifies these exact declarations and types. A
compiler import cannot supply them, even from the platform's real
`<pthread.h>`. A valid joinable handle
held only by this parent, with no detach, cancellation, competing join, or
self-join, is assumed to join successfully; this assumption must be scoped to
those preconditions by a checked rule. Thread creation may fail and must not
transfer ownership on failure. The thread body and both client paths remain
verification obligations. A native compiler run below checks C syntax only;
it does not establish any concurrency property.

## Sequential worker checkpoint

`mdtests/fork_join_worker_sequential.md` verifies `fill_range` from the frozen
source with the contract a spawn transfers as the worker's task. That earlier
sequential proof alone made no concurrency claim.
`mdtests/fork_join_worker_direct_contract.md` verifies the same worker with
direct `views`/`owns` clauses; its generated certificates expand and reverify.
The complete example sidecar uses that direct contract for its checked spawns.

## Frozen fork/join program

`fill_parallel` requires a live four-element output array. The parent zeros
it before starting either thread. `fill_range` is one reusable worker over a
half-open interval: one child writes indices `[0, 2)` to 11, and the other
writes `[2, 4)` to 22. The stack-allocated job records and the output array
remain live until every created child is joined. On success the function
returns 1 with output `[11, 11, 22, 22]`. If the first creation fails it
returns 0 with all zeros; if the second fails it joins the first before
returning 0 with `[11, 11, 0, 0]`. There is no parent read after spawn or
free/return of a child-borrowed object before its join.

The [example](../../examples/concurrency-fork-join/) proves the exact output
contents for all three outcomes and ownership of the output buffer at return.
The modeled create/join rules transfer disjoint output slices, borrow each
stack job until join, and reject overlapping writes or premature parent access.
Shared-reader companions and hostile source regressions exercise both join
orders, cleanup, and refusals. These are client claims conditional on a C
library that implements the trusted modeled pthread runtime specification.

On the selected Linux toolchain, the source-only syntax check is:

```sh
gcc -std=c11 -pthread -funsigned-char -D_POSIX_C_SOURCE=200809L \
  -Wall -Wextra -Werror -fsyntax-only examples/concurrency-fork-join/fork_join.c
```

The local macOS syntax smoke used Homebrew Clang 19.1.7 with the same source
and options; it is not evidence for the selected Linux ABI or runtime.
