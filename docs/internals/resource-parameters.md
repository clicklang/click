# General proof parameters and resource contracts

Status: proposal for review, not accepted parser syntax. This extends
[mutex operations as resource contracts](mutex-resource-contracts.md). The
language reference continues to describe implemented behavior.

## Immediate implementation scope

The concurrency implementation starts with `P: Resource` on named contracts
and C sidecars, resource descriptions as explicit arguments, and P in ownership
clauses and `mutex_use<P>` / `mutex_live<P>`. It does not add value parameters,
higher-order families, generic theorems or packaging declarations, inference,
or the contract-header migration below. Existing storage checks remain in use;
named memory transport is a later step. The public `guarded_by(P, mu)` query is
also deferred until generic initializing helpers need it. Concrete publication
continues to check the resource declaration's existing `guarded_by` annotation.

The first kernel checkpoint extracts a shared `ResourceDescription` from the
mutex-specific interface. It retains a declared instance's family, evaluated
arguments, and field schema, excluding its occurrence identity and observed
fields. The kernel transition for declared invariant restoration checks that
description and actual ownership; an explicitly supplied owned replacement
with the same description is valid. Current runtime unlock still selects the
original named instance; selecting a replacement from a proof awaits the named
`state` call interface. A missing
instance or a different family, arguments, or schema is rejected. Guard and
initialization checks remain separate.

This checkpoint does not accept `<P: Resource>` source syntax. A verified
function rule currently contains a concrete interface. The next kernel layer
must certify an opaque resource parameter once and check instantiation of its
resource transfers and memory effects. Treating an unknown P as having an empty
footprint, or rechecking just the concrete instantiations found in a project,
would not implement the proposed generic rule.

## Recommendation

Use one explicit proof-parameter list, `<name: kind, ...>`, for declarations
that need parameters beyond their ordinary arguments. Keep ownership entirely
in `owns`, `views`, `consumes`, and `produces`. Normalize named contracts to the
same resource clauses and call maps that C sidecars already use.

```text
resource package<P: Resource>() {
    owns item: P;
}

contract Preserve<P: Resource> for void() {
    owns item: P;
}

void helper<P: Resource>(void* context) {
    owns item: P;
} by { ... }
```

`P` describes a resource. `item` names an owned instance of that resource.
Passing `P` supplies no ownership. This distinction is the central rule, for
user-defined resources, memory, and mutex authority alike.

## Three meanings that must stay distinct

| Declaration | Argument means | What the parameter permits |
| --- | --- | --- |
| `T: Type` | A Click type, such as `Integer` | Using `T` as a type. |
| `n: Integer` (or another supported Click value type) | A specification value | Using that immutable value in specifications. |
| `P: Resource` | A resource description, such as `counter_state(counter)` | Stating resource clauses involving `P`. |
| `owns item: P` | An actual owned instance supplied to the call | Using and returning that authority under the contract. |

`Type` and `Resource` are parameter kinds. They are not C types, heap objects,
or model-field types. Existing `<T>` type parameters remain shorthand for
`<T: Type>`; existing applications such as `List<int32>` keep their spelling.
Do not rename `Integer`, `resource`, or the ownership clauses.

The general parameter facility initially supports these first-order kinds.
It does not add higher-order predicate arguments, resource-family functions,
resource lambdas, or arbitrary propositions as values. A later family
parameter taking an address would need an explicit signature; it must not be
silently confused with the already-applied description `counter_state(p)`.

`Resource` is the recommended spelling rather than `Assertion`: it matches
`resource` declarations and the things accepted after `owns`. Documentation
should say *resource description*, not imply that it is an owned resource or
an unrestricted separation-logic formula.

## Declaration and application syntax

Place proof parameters immediately after the declaration name. Extend this
form to resources, named contracts, theorems, pure functions, and C sidecars
where their existing semantics admit the parameter kind. The parameters do
not alter the imported C signature, ABI, or source code.

```text
resource package<P: Resource>(label: int32) {
    owns item: P;
}

contract Bounded<P: Resource, limit: Integer> for int32() {
    owns item: P;
    ensures to_integer(result) <= limit;
}
```

Ordinary resource arguments still use `name: type` in parentheses. The angle
list holds the additional proof parameters; a resource application remains
`package<counter_state(counter)>(7)`. Ordinary value arguments need not migrate
into angle brackets. Do not introduce separate angle-list syntaxes for mutexes,
resource declarations, and contract declarations.

Applications use the same argument positions:

```text
step(helper<counter_state(counter)>(context), { item: state });
step(Bounded<counter_state(counter), 10>, { item: state });
```

The first selects an actual C call; only `context` is a C argument. The second
selects a named contract for the callback at the current C frontier, following
the existing contract-selection rules. The map passes actual owned instances.
Angle arguments never pass ownership, and a map never silently declares `P`.

A resource argument is parsed in a resource-description context after resolving
the declaration and expected parameter kind. Thus `counter_state(counter)` is
not a C function call, and a memory range such as `p[0..n]` is a description of
memory authority. Unknown names and kind errors are diagnosed before proof
search. C sidecar parsing must recognize this form without changing the C
frontend's grammar.

Proof parameters are in scope in ordinary parameter types and contract bodies;
ordinary parameters are in scope in body clauses. This scope rule does not
permit an arbitrary `T` to change an imported C signature: C sidecars must
retain its concrete parameter and result types. Generic Click data and resource
declarations can use `T` in their ordinary parameter types. Parameter declarations may
refer to earlier proof parameters, not forward references or later C argument
names. At a call, actual descriptions may mention caller values: those values
are captured at that call's entry. `P` is fixed within that instantiation.

Inference may omit the whole angle list when the explicitly supplied resource
binders determine a unique substitution. For example, supplying `item: state`
can determine `P` from the checked type of `state`. Inference is structural
matching, not proof search or a search for convenient owned resources. Check
all occurrences of a parameter for agreement. An output alone cannot infer a
missing description. The explicit form must always be available and printed
in an ambiguity diagnostic. Partial argument lists and defaults are deferred.

## Normalize the existing named-contract interface

Today a named contract can declare an instance in its proof-parameter list:

```text
contract Exact(cell: Counter()) for int32() {
    owns cell;
    ensures cell.revision == old(cell.revision) + 1;
}
step(Exact(k));
```

Replace that form with:

```text
contract Exact for int32() {
    owns cell: Counter();
    ensures cell.revision == old(cell.revision) + 1;
}
step(Exact, { cell: k });
```

Also normalize `contract int32 Name(...)` to `contract Name for int32(...)`.
There is then one named-contract header, and its angle list contains genuine
proof parameters. Owned instance binders belong in clauses, exactly as they do
in C sidecars. Produced binders use the existing output pattern. The existing
`as { cell: k }` on a contract-refinement conclusion still introduces the
target's arbitrary resource binders; it does not instantiate proof parameters.
A contract fact such as `Exact(callback)` retains its meaning. A generic one
is written `Preserve<P>(callback)`.

Recommend migrating these forms together while dependencies are small. Give
old forms a focused migration diagnostic rather than maintaining two meanings
of “proof parameter.” No changes to C code are necessary.

## What a resource argument contains

A description identifies a resource family with its type/proof arguments and
captured ordinary arguments, or an existing primitive resource description
such as a memory range. It contains no owned occurrence, acquisition receipt,
observed model fields, current population count, or right to unfold anything.
Passing the description itself is freely repeatable. Using a resource described
by it obeys that resource's existing authority rules.

Arguments are evaluated at the explicit contract snapshot under ordinary
readability and ownership requirements. For example, choosing `R(p->next)`
requires permission to read `p->next` and captures that pointer value. A later
store cannot retarget `P`. A description is not a closure that repeatedly reads
mutable memory. Field observations captured as value arguments remain explicit
constraints; mutex publication must reject a description whose captured facts
cannot remain valid under its permitted interference.

Compare descriptions by checked family identity and arguments, including
already-proved value equalities. Use no automatic body unfolding or arbitrary
logical equivalence test. Equal descriptions still do not make two owned
occurrences interchangeable. Kernel certificates must check both levels.

A generic body can transport or package `owns item: P`. It cannot inspect
`item.value`, unfold an unknown `P`, assume its footprint is empty, duplicate
it, infer thread safety, or use `count(P)`. A generic `views item: P` would need
a separately checked viewability capability; the first implementation rejects
it rather than assuming every resource supports views. The same principle
applies to countability and unrestricted sharing. This proposal adds no new
capability syntax before one is needed.

A generic call's memory effects must also be instantiated from P. Treating an
unknown footprint as empty would incorrectly frame facts about protected or
mutable memory. Generic code has only abstract access to P; concrete footprint,
aliasing, stability, and preservation checks are still owed at instantiation.
An ordinary `owns item: P` clause does not promise unchanged model fields.

Packaging through a named owned child is instance-based, even if the wrapper
has no model fields. Apply this rule to concrete wrappers too: `package<P>`
must not become a counted population merely because it declares no fields.
Do not require a dummy model field to obtain instance semantics. Existing
counted-resource declarations retain their population semantics; a future
countable generic wrapper needs an explicit checked capability. The migration
must distinguish these cases instead of inferring countability from an empty
field list.

Instantiation exposes a concrete instance's checked field schema to its caller.
An acquired `state: counter_state(counter)` therefore has a readable `value`
field. A generic acquiring helper cannot read that field when it knows only
`state: P`. Each produced instance has fresh observations constrained by its
instantiated contract; describing `P` does not preserve an earlier value.

Named memory uses the same clause shape, for example `owns bytes: p[0..n]`.
The name selects a checked memory permission, with no invented model fields.
It can be split only through checked memory operations, not by duplicating the
name. Ordinary range validity, overlap, and storage-lifetime checks remain in
force. This is a necessary general extension, not a new mutex storage family.

## Mutex contracts use the general facility

Write `mutex_live<P>(mu)` and `mutex_use<P>(mu)`. Their extra argument occupies
the same proof-parameter position as `package<P>()`; do not add a special
second ordinary argument for mutex invariants. Keep `mutex_guard(mu)` unparameterized:
the acquisition already records its initialization and associated description.
All transitions must check that association; it is not supplied by the caller's
choice of `P`.

The following are complete transfer sketches for the successful modeled
operations. `N` and `A` below stand for the selected runtime's fixed mutex byte
size and alignment, not new free parameters or public resource families.
The C declarations still come from the runtime's actual pthread signatures.

```text
contract MutexInit<P: Resource> for int32(void* mu, void* attributes) {
    requires aligned(mu, A);
    requires guarded_by(P, mu);
    consumes storage: ((uint8*)mu)[0..N];
    consumes state: P;
    produces lifetime: mutex_live<P>(mu);
}

contract MutexLock<P: Resource> for int32(void* mu) {
    owns access: mutex_use<P>(mu);
    produces guard: mutex_guard(mu);
    produces state: P;
}

contract MutexUnlock<P: Resource> for int32(void* mu) {
    owns access: mutex_use<P>(mu);
    consumes guard: mutex_guard(mu);
    consumes state: P;
}

contract MutexDestroy<P: Resource> for int32(void* mu) {
    consumes lifetime: mutex_live<P>(mu);
    produces storage: ((uint8*)mu)[0..N];
    produces state: P;
}
```

Runtime argument validity, absence of outstanding loans at destruction,
restoration at unlock, and guard lifetime dependencies remain checked
preconditions as specified in the mutex design. These sketches do not weaken
those rules or promise success for an operating-system error outcome.

`guarded_by(P, mu)` is a proposed pure query of checked resource metadata,
reusing the existing declaration term. A `guarded_by counter->mu` declaration
establishes this fact for its instantiated description and that mutex. Merely
writing the query cannot register a new invariant or grant ownership. A
parametric initializing helper must require it; the same substituted fact is
checked at a call. Validation of that metadata must include the existing
protected-resource restrictions. Raw memory has no such annotation: use an
ordinary resource wrapper to declare its protection discipline. An empty
protected resource can similarly be an ordinary declaration with `guarded_by`.
This query is a new public fact, and should be reviewed along with the parameter
syntax rather than buried in a runtime error.

For example, a caller with checked typed lifetime `life` can write:

```text
let { guard: g, state: s } =
    step(pthread_mutex_lock<counter_state(counter)>(mu), { access: life });
```

The usual checked lifecycle-to-use loan preserves the association with `P`.
A guard escaping the call keeps its lifetime dependency until release. Unlock
requires the exact live guard and an owned witness of the full associated P,
including its arguments and any identity constraints stated by P. Merely matching
the resource family is insufficient. It need not be the original payload
occurrence: a checked replacement satisfying the same invariant is valid when
P permits it. Outstanding payload loans must still be discharged. Destruction
returns a fresh observation of `P`, not the
values observed before publication.

Existing unary `mutex_use(mu)` and `mutex_live(mu)` mean an *opaque association*,
not an empty invariant. They remain useful for existing balanced opaque helpers.
Typed authority may be borrowed through an opaque interface without losing its
association on return. An opaque interface cannot invent `P` by supplying angle
arguments at lock: require `mutex_use<P>(mu)`. There is no implicit cast back
from opaque authority to a description guessed by a proof. The same limitation
applies to destruction that tries to return typed payload. Do not introduce a
public existential syntax merely to retain these existing opaque forms.

## Diagnostics and implementation boundaries

Use the instantiated Click requirement wherever possible:

```text
Requires owns mutex_use<counter_state(counter)>(mu)
Requires owns counter_state(counter)
Requires guarded_by(counter_state(counter), mu)
Cannot infer resource parameter P; supply helper<counter_state(counter)>(...)
Expected a Resource argument for P; state is an owned instance
P has no declared field value
```

For ambiguous inference, list the conflicting binder descriptions. For stale
or mismatched authority, also show the supplied binder and its source location.
Do not describe a missing description as missing ownership, or an ownership
failure as a generic parameter inference failure. An explicit description
never repairs missing authority.

Implementation order:

1. Add checked parameter kinds, scope/substitution, and a shared resource-
   description representation. Keep descriptions out of owned-resource storage.
2. Normalize named-contract binders and call syntax, with migration diagnostics.
   Demonstrate an ordinary generic preserving contract and packaging resource
   before using the feature in mutex dispatch.
3. Extend named primitive/memory transport. Certify generic code once for an
   arbitrary description with only its declared requirements; do not certify
   only the instantiations seen in a project.
4. Carry typed descriptions through mutex initialization, modular entry,
   reborrowing, wrappers, and opaque calls. Add fresh acquisition outputs and
   the corresponding checked unlock/destruction transfers.
5. Infer omitted arguments from explicit binders only after explicit
   instantiation and diagnostics are correct.

Acceptance includes generic transport without duplication, missing-authority
refusal despite a supplied description, scope/capture tests, failed field
access on unknown P, unchanged C signatures, memory and ordinary wrapper
examples, preservation of P through nested loans, wrong-family/argument and
stale-initialization refusals, valid replacement of a fungible invariant witness,
and fresh payload observations after reacquisition.
Descriptions should be interned or persistently shared; substitution and
checking must operate on explicit arguments and deltas, not clone whole
resource environments or enumerate all generic instantiations.
