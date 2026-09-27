# Resource arguments and mutex associations

Status: revised design direction. Explicit resource-description parameters are
not part of the concurrency plan. The earlier angle-bracket proposal is
withdrawn; its syntax was never accepted by the parser.

## Pass resources through existing proof interfaces

Use existing proof-only resource arguments and named call maps. Do not add
`<P: Resource>`, parameterized mutex spellings, or a separate description
argument at a call. Do not replace these with a second description argument in
parentheses. Introduce a new parameter syntax only after a concrete use case
shows why existing resource passing is insufficient. Existing type applications
such as `List<int32>` are outside this change.

Named contracts already separate proof arguments from the C signature:

```text
contract Read(cell: marked_cell(p)) for int32(int32* p) {
    owns cell;
}
step(Read(s));
```

The proof argument selects an instance. The `owns` clause determines its
ownership treatment; passing a name alone does not create authority. C sidecars
use their existing named call maps, such as `step(helper(p), { item: s })`.
Retain both implemented forms. A general contract-header migration is not a
prerequisite for concurrency.

These examples illustrate existing interfaces, not a newly accepted generic
resource declaration syntax. A helper whose resource family is unknown may
need further contract expressiveness. Establish that need with a concrete
helper before choosing new syntax.

## Descriptions remain internal metadata

The verifier must distinguish a resource description from ownership of an
instance satisfying it. For example, `counter_state(counter)` identifies the
family and captured arguments; an owned instance also has an occurrence
identity and current field observations. This distinction does not require
users to supply two arguments.

Derive the description from a supplied checked resource. Retain it in the
mutex initialization and its associated lifetime, use, and acquisition
authorities. A later operation must check that association, not reconstruct it
from the mutex address or a caller's guess about the resource family.

Compare descriptions using the checked family, arguments, and schema, including
argument equalities already proved by the verifier. A description grants no
ownership, field access, viewability, countability, or thread safety. An unknown
representation has an unknown memory footprint, not an empty one.

## The four mutex operations

The ordinary contract binders are specified in
[Mutex operations as resource contracts](mutex-resource-contracts.md).

| Operation | Resource arguments and association |
| --- | --- |
| Initialize | Consume the supplied folded `state` and storage; derive and record the protected assertion; produce `lifetime`. |
| Lock | Borrow the supplied `access`; obtain the protected assertion from its checked initialization association; produce `guard` and freshly observed `state`. |
| Unlock | Borrow `access`; consume the matching `guard` and an owned `state` satisfying the associated assertion. |
| Destroy | Consume `lifetime` after recovering all uses and acquisitions; return storage and freshly observed `state`. |

The target call shape for acquisition is:

```text
let { guard: g, state: s } =
    step(pthread_mutex_lock(mu), { access: life });
```

This remains a target, not implemented protected-state output syntax. The
checked lifetime-to-use loan determines the association. There is no separate
resource-description argument to infer or supply.

Initialization continues to check the supplied resource's `guarded_by`
annotation. No new public `guarded_by(P, mu)` query is required by this plan.
Unlock requires the exact acquisition and actual ownership of the full
protected assertion. A replacement instance is valid when that assertion
permits it; matching only the family is insufficient. Outstanding payload
loans must still be discharged. Returning ownership does not preserve old
field observations without a contract guarantee.

## Independent helpers and diagnostics

An independently checked helper receives only the information its contract
provides. A use permission with an opaque association must preserve that
association through loans and returns, but does not expose a guessed payload
schema. The implementation must establish how a helper's input authority
determines its output resource before enabling protected-state outputs.
Concrete call-site information alone cannot justify a generic body proof.

### Concrete helper boundary: proposed refinement

Status: surface decision pending review. The following `protecting` modifier
is a proposal, not accepted syntax. It adds a requirement on an existing
authority argument; it does not add a proof argument or a resource-description
value. Do not implement this spelling until reviewed.

Consider existing C helpers that only lock and unlock a counter's mutex:

```text
void counter_lock(struct counter *counter) {
    pthread_mutex_lock(&counter->mu);
}
void counter_unlock(struct counter *counter) {
    pthread_mutex_unlock(&counter->mu);
}
```

Assume `counter_state(counter)` is an exclusive resource whose declaration
contains `guarded_by counter->mu;`. Proposed sidecar contracts are:

```text
void counter_lock(struct counter *counter) {
    owns access: mutex_use(&counter->mu)
        protecting counter_state(counter);
    produces guard: mutex_guard(&counter->mu);
    produces state: counter_state(counter);
}

void counter_unlock(struct counter *counter) {
    owns access: mutex_use(&counter->mu)
        protecting counter_state(counter);
    consumes guard: mutex_guard(&counter->mu);
    consumes state: counter_state(counter);
}
```

The extra requirement is necessary information. `guarded_by` checks where a
resource may be published; it does not prove that an arbitrary input mutex
was initialized with that resource. Two different resource families may name
the same mutex in their declarations. The input must distinguish them, and
must distinguish different captured arguments within one family.

The proposed modifier states that this authority's initialization protects the
specified assertion. It grants no current ownership of `counter_state`, and
does not constrain its observed fields. Bare `mutex_use(mu)` remains valid
for helpers that do not need to know the protected assertion. The existing
`mutex_use_named_payload_read` fixture demonstrates that bare use authority
does not justify reading the payload even after locking.

At a call, the caller still passes only actual resources:

```text
let { guard: g, state: s } =
    step(counter_lock(counter), { access: u });
step(counter_unlock(counter), { access: u, guard: g, state: s });
```

Here `u` is the caller's existing use authority. There is no additional
`counter_state(counter)` argument to either call. Initialization still derives
the association from the actual resource it consumes.

### Checking the proposed helper contracts

The implementation would have to establish all of the following:

1. **Entry.** Independently checking `counter_lock` assumes a fresh abstract
   initialization and a rooted use input carrying exactly the stated
   association. No protected-state ownership or field observations exist yet.
   Validate the assertion's declaration and `guarded_by` pointer before
   admitting that association. It is a contract premise, checked at every
   call, not an inference from the helper's desired result.
2. **Acquisition.** Runtime lock checks the input's loan and initialization,
   creates an exact guard, and supplies a fresh state instance satisfying the
   associated assertion. Its observations are arbitrary subject to that
   assertion, never copied from a previous acquisition. Runtime calls and
   helper bodies use this same transition.
3. **Return.** Returning guard and state exports the checked acquisition and
   retains its lifetime dependency. Merely finding two matching resource
   shapes at return is insufficient. The caller must receive the acquisition
   evidence, including its outstanding loan hold, with the resources.
4. **Release entry.** Independently checking `counter_unlock` requires a
   guard for this input protocol and ownership of the stated resource.
   At a call, check that the supplied guard belongs to this initialization
   and acquisition; the same address alone is insufficient. A replacement
   state instance is permitted if its full assertion matches.
5. **Release.** Consume that guard and the owned, restored state, discharge
   the acquisition's hold, and return the use authority. Outstanding payload
   loans prevent restoration. The checked transition must be transported
   back to the caller so destruction cannot overlook an escaped acquisition.

An association failure should state the requirement in contract terms, for
example `Requires owns mutex_use(&counter->mu) protecting
counter_state(counter)`, followed by the supplied authority's actual protected
assertion. Missing guard or state ownership keeps the ordinary `Requires`
diagnostic. A valid assertion with an unsupported transfer form is an
unsupported-feature diagnostic, not a claim that the C implementation is wrong.

Do not infer an extra input requirement just from a produced state and its
`guarded_by` annotation. That would make a postcondition silently strengthen
the precondition, and it would not cover a helper that locks, reads, and
unlocks internally without returning state. Requiring ownership of the state
on entry would also be wrong: it is escrowed while the mutex is unlocked.

This proposal addresses concrete resource families first. General helpers
that preserve an unknown association can continue to use bare authority.
Returning or inspecting an unknown payload remains separate work; this
proposal does not activate the dormant resource-parameter machinery.

Prefer precise existing requirements in failures:

```text
Requires owns mutex_use(mu)
Requires owns mutex_guard(mu)
Requires owns counter_state(counter)
Requires owns mutex_live(mu)
```

For an association mismatch, identify the supplied binder and its actual
protected resource alongside the required resource. Do not ask the user to
supply a description argument to repair missing ownership or lost association.
Distinguish a missing resource from an unsupported contract form.

## Implemented groundwork and next work

`ResourceDescription` already separates family, captured arguments, and schema
from occurrence identity and observed fields. Declared mutex restoration checks
that description and actual ownership. The lower-level transition accepts an
explicit owned replacement; current runtime unlock still selects the original
instance until named `state` input transport is connected.

The kernel also has staged opaque parameter atoms and description-substitution
helpers. They are not a source-language feature: generic rule issuance and
parameter-clause evaluation remain disabled. Their existence is not a reason
to introduce explicit description parameters, and activating them is no longer
a prerequisite for the mutex migration. Reuse internal pieces only where the
resource-passing design needs them.

Next, carry the checked protected-resource association through the ordinary
named authority interface and connect runtime `state` inputs and outputs.
Keep runtime contracts and user-defined helpers on the same resource transfer
rules. Extend named storage transport using ordinary memory authority when
needed. Preserve the existing C source and ABI.

Acceptance includes association preservation through calls and reborrows,
rejection of wrong resources and stale acquisitions, fresh observations after
acquisition, checked replacement on release, and refusal to destroy while
loans or guards survive. Scope and memory-effect checks must remain bounded
and operate on explicit inputs and state changes, without copying whole resource
environments or enumerating all concrete callers.
