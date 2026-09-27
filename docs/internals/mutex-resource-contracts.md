# Mutex operations as resource contracts

Status: design with an implemented named lifecycle checkpoint described below.
The complete transfer scheme remains the design direction; protected-state
transport and storage binding syntax still need implementation.

Mutexes should behave like resources described by ordinary Click contracts.
Their runtime implementation needs trusted rules, but their proof inputs and
outputs should not need a separate naming convention or special `step` syntax.
This document specifies initialization, acquisition, release, and destruction
together so that one operation's outputs fit the next operation's inputs.

This refines [Concurrency contracts and failure explanations](concurrency-contracts-and-diagnostics.md).
For the public contract design, it supersedes the hard-coded initialization
binder `invariant` and the tentative lock output names `invariant` and
`protected`. It does not change their implementation by itself.

## Ordinary contracts determine the proof interface

`pthread_mutex_lock` is a pthread library function, not a C language builtin.
Click's selected runtime gives it a trusted specification. That specification
should expose a contract with ordinary named resource binders, just as a
user-defined function's sidecar does.

In an ordinary contract, `produces item: R` lets a caller write
`let { item: x } = step(...)`. The name `item` belongs to the contract; `x` is
chosen by the caller. The produced resource is independent of the function's C
return value. A mutex operation should follow exactly that rule: `step` must
not invent an output because it recognizes a word such as `protected`.

The standard runtime contracts choose the names below. User-defined contracts
may choose different binder names for the same resource types.

| Contract binder | Resource | Meaning |
| --- | --- | --- |
| `lifetime` | `mutex_live(mu)` | Exclusive lifecycle authority for one initialization, including responsibility for destruction. |
| `access` | `mutex_use(mu)` | Permission to use that initialization while its lifetime is guaranteed. |
| `guard` | `mutex_guard(mu)` | Ownership of one particular acquisition. |
| `state` | The user-defined protected resource | Ownership of the protected data and its currently observed values. |
| `storage` | Existing exclusive memory authority for the mutex representation | Storage consumed by initialization and recovered by destruction. |

The last row names an ordinary memory input/output, not a proposed
`mutex_storage` resource. Its exact range syntax and support for naming raw
memory authority must follow the general memory-resource interface.

An *invariant* is the assertion that must hold whenever the mutex is unlocked.
A `state` instance owns resources satisfying that assertion. Locking returns
ownership of such an instance; it does not return an assertion as a value.
The invariant is not a C argument, a mutable field snapshot, or a new kind of
ownership clause.

## The invariant association

Write `P` in the sketches below for a resource assertion such as
`counter_state(counter)`: the resource family and its parameters, without an
instance binder or observed field values. `P` is explanatory notation, not an
accepted Click type parameter or a new resource named `P`.

Initialization binds one `P` to one fresh mutex initialization. Both lifecycle
authority and borrowed use authority retain that association. A helper checked
independently of its callers must know this association before it can acquire
protected state. A call must check the association against the supplied
initialization; matching the printed mutex address is insufficient.

The revised direction is described in
[Resource arguments and mutex associations](resource-parameters.md). Pass
resources using existing proof arguments and named call maps. Derive the
protected assertion from the checked input authority; do not require a
separate description argument or add angle-bracket resource parameters.

In the sketches below, `P` remains explanatory notation for that recorded
assertion. The unary `mutex_live(mu)` and `mutex_use(mu)` spellings retain the
association internally. How an independent helper exposes the associated
payload in its contract must be established before enabling those outputs;
an opaque input must not be treated as a known concrete payload.

## The four runtime contracts

These are semantic sketches, not parser-ready declarations. `Storage(mu)`
denotes the existing memory authority for the complete modeled mutex
representation. Its size and alignment come from the selected runtime ABI.
`P` is the assertion associated with the initialization in question. The table
states the full transfer; the subsequent sketches emphasize ordinary contract
clauses.

| Operation | Required inputs | Produced outputs |
| --- | --- | --- |
| Initialize | Consume `storage` and folded `state: P`; require alignment and valid initialization arguments. | `lifetime`; the protected state is placed under the mutex. |
| Lock | Preserve `access` for this initialization. | A new `guard` and freshly observed `state: P`. |
| Unlock | Preserve `access`; consume the matching `guard` and restored folded `state: P`. | No new resource. |
| Destroy | Consume `lifetime`; require every use loan recovered and no outstanding acquisition. | `storage` and folded `state: P`. |

### Initialization

```text
consumes storage: Storage(mu);
consumes state: P;
produces lifetime: mutex_live(mu);
```

The resource definition's `guarded_by` declaration must identify this mutex.
The caller must actually own the folded state; a resource definition or an
association alone supplies no ownership. Initialization establishes the
association from that input and gives it a fresh initialization identity.

Consuming storage removes ordinary write authority over the initialized mutex
representation. It does not consume ownership of the surrounding allocation
or unrelated fields. The lifecycle resource retains the storage dependency;
it cannot outlive the allocation or local object containing the mutex.

This is the proposed uniform ownership interface. The current implementation
also uses storage reservations; migrating those reservations must neither
return duplicate storage ownership nor lose allocation-lifetime protection.

### Acquisition

```text
owns access: mutex_use(mu);
produces guard: mutex_guard(mu);
produces state: P;
```

The guard records a fresh acquisition of this initialization. The state grants
payload ownership; the guard by itself does not grant access to the payload.
The pair carries a checked association with the same protocol and acquisition.

Observed fields are fresh on each acquisition and constrained by `P`. Earlier
observations remain descriptions of earlier states, not facts about current
memory. Reusing a local name must not reuse an old observation identity.

The use permission survives the call. The guard retains a lifetime dependency
until release, so returning from the lock call or an acquiring helper does not
make the initialization destroyable. This escaping dependency is part of the
contract transfer, not a source-level continuity witness.

### Release

```text
owns access: mutex_use(mu);
consumes guard: mutex_guard(mu);
consumes state: P;
```

Release requires the actual acquisition authority and a restored folded
instance of the associated assertion. Values may have changed while held;
they must satisfy the resource's invariant when returned. A same-address guard
from another acquisition, or a same-family state for different parameters,
cannot substitute. Outstanding payload borrows must end before release.

Folding a wrapper around the guard does not release the mutex. The wrapper
must expose the required authority through ordinary resource operations.
Likewise, renaming a local binder has no effect on acquisition identity.

### Destruction

```text
consumes lifetime: mutex_live(mu);
produces storage: Storage(mu);
produces state: P;
```

Lifecycle authority is exclusive. All loans and guard holds must be discharged
before it can be consumed. Destruction returns the protected resource and raw
mutex storage; freeing the allocation is a separate operation.

If the mutex has been shared, destruction cannot revive the values originally
supplied at initialization. Its returned state is constrained by the invariant
and any separately established guarantees, not by stale observations.
Reinitializing the same address creates a different initialization.

An empty mutex follows the same protocol with the empty protected assertion.
There is no payload ownership to expose. The exact surface treatment of the
trivial `state` binder must be specified together with ordinary empty-resource
contracts; it should not introduce another mutex-specific output convention.

## Call syntax follows from those contracts

With an available named use instance `u`, ordinary named input and output
transport gives the following proposed proof steps:

```text
let { guard: g, state: s } =
    step(pthread_mutex_lock(mu), { access: u });

// Unfold s, verify the C operations, and restore the folded state.

step(pthread_mutex_unlock(mu), {
    access: u,
    guard: g,
    state: s
});
```

The input map names resources already owned; the output pattern introduces
new instances. `guard` and `state` are declared contract outputs, not reserved
keys understood only by the mutex dispatcher. The C call still returns its
ordinary status code. Its proof resources do not become additional C results.

Once ordinary storage binders are supported, initialization and destruction
would have the corresponding shape:

```text
let { lifetime: life } = step(pthread_mutex_init(mu, 0), {
    storage: bytes,
    state: initial
});

// Checked borrowing of life supplies use authority for calls.

let { storage: bytes_after, state: final } =
    step(pthread_mutex_destroy(mu), { lifetime: life });
```

These examples do not establish new syntax for introducing `u` or `bytes`.
Those introductions need general loan and memory binding rules. The existing
checked conversion from lifecycle authority to a synchronous use loan should
remain available, but its interaction with explicit named input maps must be
specified. It must select supplied authority rather than search for a
convenient matching instance, and an escaping guard must retain the loan.

The former initialization spelling
`step(pthread_mutex_init(mu, 0), { invariant: initial })` was a hard-coded
selection hook. It has been replaced by schema-declared state input and lifetime
output transport. The complete storage transfer and protected-state association
remain pending; renaming the key alone would not complete the migration.

## Preserving, replacing, and packaging resources

An ordinary helper with `owns guard: mutex_guard(mu)` preserves that acquisition.
Unlocking and relocking cannot satisfy that promise. A helper that replaces an
acquisition must consume an input guard and produce a new output guard, just
as it would replace any other resource occurrence.

User-defined wrappers may package a guard and protected state together. They
may also package lifecycle or use authority subject to the ordinary lifetime
rules. Folding a wrapper changes the presentation of owned resources; it does
not initialize a mutex, acquire it, grant access, or discharge a loan.

The selected runtime supplies the default contracts. User-defined helpers can
use the same clauses and binding machinery. Trusted code remains responsible
for the actual mutex transition, fresh identities, interference, and storage
effects; it must not bypass ordinary resource input/output validation.

The current modeled runtime assumes successful valid operations under its
checked preconditions. These sketches do not prove the operating system's
implementation, absence of deadlock, or termination. A runtime profile that
models failure or a future try-lock operation needs outcome-dependent resource
contracts: failure cannot produce a successful acquisition's guard or state.
The status result and resource outputs must describe the same outcome.

## Failures should name the missing requirement

Missing authority should use existing Click resource terms:

```text
Requires owns mutex_use(mu)
Requires owns mutex_guard(mu)
Requires owns counter_state(counter)
Requires owns mutex_live(mu)
```

An association mismatch should identify the supplied authority and its
protected resource, alongside the required resource such as
`counter_state(counter)`. Matching by address must not suppress this failure,
and a separate description argument must not be offered as a repair.

Where a supplied occurrence is incompatible, identify it and its source: the
required entry guard versus the newly acquired guard, or the lifetime whose
loan remains outstanding. Do not invent a `not_held` fact just to phrase a
protocol failure as a missing proposition. Report the outstanding resource or
loan and its source location. Distinguish an unsupported contract form from
missing ownership.

The checker may track generations, receipts, and loan identities internally.
Ordinary diagnostics should name the relevant Click resources and binders,
not expose those implementation structures.

## Current boundary and implementation sequence

The runtime now declares one shared binder schema for all four operations.
Implemented projections pass through the ordinary parser's supplied/produced
binder checks. Initialization's named form is:

```text
let { lifetime: life } = step(pthread_mutex_init(mu, 0), { state: initial });
step(pthread_mutex_destroy(mu), { lifetime: life });
```

The kernel independently checks those maps and binds the output to the actual
owned initialization. Named preserving `owns life: mutex_live(mu)` and
`owns g: mutex_guard(mu)` helpers are implemented. Names select exact authority;
they have no fields or body to unfold. Checked preserving calls reconnect each
name only to the same returned authority. Old lifecycle names fail after
destruction and reinitialization at the same address.

Direct unary preserving `mutex_use` contracts support balanced opaque
lock/unlock, exposing no protected state. Named use inputs are supported:
`owns access: mutex_use(mu)` accepts an explicit named use or lifecycle authority.
The call borrows the selected authority, binds a scoped callee use permission,
and restores the caller's original authority and name after checked recovery.
Nested reborrows select the same exact source; matching only the mutex address
cannot substitute a sibling permission.

General consuming/producing helper contracts, named storage, fresh protected-state
outputs, and escaping guards remain pending. Concrete lock still retrieves the
escrowed instance; calls without named runtime maps retain their prior checked
behavior. The contract sketches above describe the complete target, not the
currently supported subset. New runtime projections must be enabled only when
their corresponding kernel transfer is implemented.

Implement the design in this order:

1. Use existing resource arguments and named binders, deriving the protected
   assertion from checked inputs. Establish how independent helper contracts
   retain that association before enabling protected-state outputs. Do not make
   a general parameter syntax a prerequisite.
2. Route runtime contract inputs and outputs through ordinary binder checking.
   Validate missing, extra, unowned, and incorrectly typed inputs exactly as
   for user-defined contracts. Remove the special initialization key.
3. Carry the invariant association through initialization, independent helper
   entry, checked calls, reborrows, and wrappers. Reject stale initializations
   and mismatched resource families or parameters.
4. Produce fresh guards and protected observations on acquisition; require
   restoration on release. Check modular memory effects so callers cannot
   retain stale payload or representation-byte facts.
5. Support escaping guard lifetime dependencies and destruction/storage
   recovery. Verify consuming/producing helper contracts and their certificates,
   including exceptional exits and outstanding payload borrows.

Each stage needs negative certificate tests as well as surface examples.
Acceptance includes a user-defined acquiring/releasing helper whose interface
uses the same rules as the runtime contract, reacquisition that cannot recover
an earlier value without proof, failed substitution of a different guard, and
refusal to destroy while any acquisition or use loan survives. Preserve
existing C as the regression boundary. Do not rewrite C into a more convenient
proof shape.

Shared worker execution, loop assertions with conditional acquisition,
conserved contribution accounting, and atomic publication remain separate
semantic work. Completing these four resource interfaces is necessary for
that work, not evidence that it is already implemented.
