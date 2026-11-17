# Resource arguments and mutex associations

This design record covers how mutex contracts name the resources they protect
by passing resource types as arguments.

Status: resource types are accepted as mutex-use arguments. The earlier
angle-bracket proposal is withdrawn; its syntax was never accepted by the parser.
Acquiring and releasing helpers use these types with existing
[`owns`/`consumes`/`produces` contracts](mutex-resource-contracts.md#acquiring-and-releasing-helpers).
The chronological investigation below records earlier proposals, not additional
language features to implement.

## Resource types in mutex contracts

The accepted surface terminology is **resource type**. `counter_state(counter)` is a
resource type; an owned instance has that type and currently observed fields.
A resource type carries no ownership and no field observations. Resource types
can be used as arguments without a separate function proof parameter:

<!-- verified-example: mdtests/mutex_use_resource_type.md -->
```click
owns access: mutex_use(&counter->mu, counter_state(counter));
```

This contract shape is implemented for modeled mutex use. No new keyword,
angle-bracket parameter, or function header is required. At an executing call,
the supplied permission must authenticate the required resource type against
the actual initialization or an already checked typed input. A unary
`mutex_use(mu)` cannot establish the stronger requirement.

Acquisition uses the existing named runtime contract outputs:

<!-- verified-example: mdtests/mutex_use_resource_type.md -->
```click
let { guard: guard, state: state } =
    step(pthread_mutex_lock, { access: access });
unfold(state);
step();
let restored = fold(counter_state(counter), { value: counter->value });
step(pthread_mutex_unlock, {
    access: access, guard: guard, state: restored
});
```

The acquired instance has fresh field observations. Unlock requires an owned,
folded instance of the protected type; it may be a replacement instance. A
summary call using the typed permission also forgets the concrete escrow's
old fields and memory observations. Neither passing the type nor retaining an
old instance name supplies current ownership.

Initial implementation boundaries: the protected type must be a declared,
field-bearing, unconditional leaf resource; its memory
footprint must not depend on changing model fields. Model fields currently
support C and integer types. Nested type/reference arguments, owned children,
and resource-type parameters on user-defined resource constructors remain
unsupported and are rejected. As with the concrete mutex path, unlock currently
requires outstanding memory loans to have returned. Named lock/unlock payload transport currently
applies to independent typed-use contracts; the existing implicit concrete
mutex path remains available. Typed permissions also cross worker boundaries:
create retains a parent share, transfers a checked worker share, and leaves
both unchanged on failure. Joins return shares into the current ledger in
either order; only complete recovery returns lifetime authority. No additional
surface syntax is needed. Parent acquisitions and releases forget protected
observations while workers remain outstanding.

The unchanged worker and parent safety proof live in
`design/concurrency-probes/mutex_counter.click` and the
`mdtests/mutex_counter_worker.md` regression. Exact final-count accounting
remains unproved: permission recovery alone does not establish two increments.

The older named-instance argument work below remains supported. It identifies
an occurrence, whereas a resource type permits replacement occurrences. The
proposed extra worker proof parameter is superseded by the nested type above.

## Pass resources through existing proof interfaces

Use existing proof-only resource arguments and named call maps. Do not add
`<P: Resource>`, parameterized mutex syntax, or a separate description
argument at a call. Do not replace these with a second description argument in
parentheses. Introduce a new parameter syntax only after a concrete use case
shows why existing resource passing is insufficient. Existing type applications
such as `List<int32>` are outside this change.

A named contract declares each resource handle with a named `owns` or
`consumes` clause, after the C signature it describes:

```text
contract int32 Read(int32* p) {
    owns cell: marked_cell(p);
}
step(Read, { cell: s });
```

The application map binds the handle to an instance by name. The clause that
declares the handle also determines its ownership treatment. Concrete calls
use the same named map, such as `step(helper, { item: s })`.

These examples use concrete resource families. A helper whose resource family
is unknown may need further contract expressiveness; that remains outside
this extension.

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
    step(pthread_mutex_lock, { access: life });
```

This remains a target, not implemented protected-state output syntax. The
checked lifetime-to-use loan determines the association. There is no separate
resource-description argument to infer or supply.

Initialization establishes the association from the owned state and mutex.
Protected resources need no mutex annotation, and no public association query
is required.
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

### Investigation: reuse ordinary resource interfaces

The proposed mutex-only `protecting` modifier is withdrawn. The illustrative
`access.state == counter_state(counter)` expression is also not an accepted
feature or a chosen design. First establish how ordinary resource definitions
and resource arguments can express the relationship. Do not introduce either
syntax as an implementation shortcut.

The current implementation has these distinct capabilities:

| Mechanism | What it establishes | What it does not establish |
| --- | --- | --- |
| Initialization with `{ state: state }` | Consumes an owned instance and records its assertion for the fresh initialization. | Does not expose that association in an independent helper's unary authority requirement. |
| Ordinary named child ownership | A parent owns a child; unfolding transfers that ownership to the proof. | Does not model state accessible only after a lock transition. |
| Ordinary resource fields | Store C values, mathematical integers, or algebraic model values. | Cannot currently hold a resource reference. |
| Named-contract resource handles | Declare a resource binder in an `owns` or `consumes` clause, bound by name at a call. | Cannot declare a reference-only handle, and do not supply transport of references to escrowed resources. |

The last distinction is important. Every contract handle is declared by the
clause that owns or consumes it, so a contract has no reference-only handle.
The retired parameter-list syntax could declare one, but only as a
declaration: nothing transported it. `ResourceCallApplication::bind` in
`src/kernel/functions.rs` checks current ownership of the actual instances it
binds, and the consumed-instance regressions reject passing an instance after
its ownership was given up. A reference-only handle needs its own declaring
clause, which belongs to the reference-transport design.

Resource declarations now accept trailing resource-valued parameters using
the same binder notation. Resource fields still have only C, integer, and
algebraic types: passing a resource reference does not make it a model field.
Changing only a mutex resource definition is still insufficient because
reference-only contract transport remains to be implemented.

Mutex authorities themselves are kernel resource atoms, not ordinary Click
resource definitions with an inspectable protected-state child or field.
`InitializedMutexInterface` records the association in the mutex ledger, and
`MutexUseCallTransfer` can retain that checked metadata when borrowing a
concrete input. `AssumedMutexProtocol`, used for independent helper proofs,
deliberately exposes no protected assertion. This is the implementation gap
behind the helper example; initialization itself already has sufficient
surface syntax.

A wrapper that merely owns `mutex_use(mu)` cannot add the missing premise.
Adding an owned `counter_state(counter)` child would require the caller to
supply that state while it is escrowed, and unfolding would expose it without
locking. Adding a tag naming the resource family would not authenticate the
association with the actual initialization. Neither is an adequate workaround.

The resource-argument implementation below establishes reference passing in
ordinary resource definitions. Extending contract transport remains the next
boundary. Such a reference must not grant payload fields or memory
access, duplicate ownership, or preserve observations across acquisition.
It must also support restoring a replacement instance satisfying the assertion:
the present mutex semantics do not require the same occurrence on every
release. Do not accidentally replace that rule with fixed instance identity
when introducing a reference.

Work through a user-defined resource managing another resource alongside the
mutex example before choosing the representation. The required outcome is an
association expressible by the resource's interface, authenticated when that
resource is constructed and checked at calls. Whether this can use existing
notation throughout remains open; there is no established need for new
keywords, angle parameters, or a separately supplied description value.

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

## Ordinary resource arguments

A resource declaration can take a named exclusive resource after its value
parameters, using the same binder notation as contract resource handles:

```text
resource revision_record(p: int32*, target: cell(p)) {
    field revision: int32;
}
```

`fold(revision_record(p, target), { revision: target.revision })` records a
reference to `target`. It does not consume `target`. The reference retains its
identity, family, captured arguments, and schema, but no observed field values.
The expression reading `target.revision` still needs the existing field-access
justification; passing the reference does not supply one.

To own the argument, use the existing child-resource rules:

```text
resource revision_owner(p: int32*, target: cell(p)) {
    field revision: int32;
    owns target;
    fact target.revision == revision;
}
```

Folding checks and consumes that particular child. Unfolding restores it with
the state described by the parent's current model. A reference captured before
a child's field changed cannot restore the old observation. The ordinary rule
requiring child fields to be related to parent fields still applies; this does
not introduce implicit existential model packaging.

The first implementation retains several explicit limits: declarations with
resource parameters must have fields, reference parameters follow value
parameters, matched resource bodies are not supported, and reference
parameter types cannot themselves take resource arguments yet. Fields select a
member's form, not whether its family can be counted. Named-contract call transport still requires
owned input instances; transporting a reference to escrowed state requires a
separate change to contract entry and refinement checking. Typed mutex permissions use resource types directly, as described above;
they do not require an owned reference to escrowed state.

## Current implementation and remaining work

Typed `mutex_use(mu, R(args))` permissions carry the checked protected-resource
association through calls and reborrows. Acquisition produces fresh protected
observations and release accepts a restored instance of the same resource
type. The implemented helpers, worker create/join transfer and population
controls are described in [Mutex resource contracts](mutex-resource-contracts.md).
The [counter proof](https://github.com/clicklang/click/blob/master/design/concurrency-probes/README.md)
uses these rules to establish two conserved increments.

This supersedes the old proposal to transport resource descriptions as
function proof parameters and the instruction to connect ordinary typed state
transfer. Named storage transport and destruction's named state output remain
proposals in the mutex contract design. New transport must preserve resource
type, initialization/acquisition identity and actual authority, with fresh
observations after acquisition and no recovery while loans or guards survive.

The [historical investigation](https://github.com/clicklang/click/blob/2175760b9/docs/internals/resource-parameters.md)
retains the withdrawn syntax and staged implementation notes. It is not an
additional interface or backlog.
