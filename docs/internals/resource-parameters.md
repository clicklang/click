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
