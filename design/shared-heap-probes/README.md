# Shared-parent ownership proof

This source-backed probe for the P1
[shared-heap-graph demo](../../issues/shared-heap-graph-demo.md) uses explicit
population authority. Its
[`shared_parent.c`](shared_parent.c) remains the frozen sequential C source.
The sidecar [`shared_parent.click`](shared_parent.click) describes initialization,
retain, branch-on-count release, parent attachment, payload reads, detachment,
and both complete destruction orders.

## Program and verification boundary

Each pipeline allocates one child and two parents, attaches both parents to the
child, drops the creator reference, destroys one parent, reads through the
survivor, and destroys the remaining parent. Success returns the original
payload. Every allocation-failure path releases only what it acquired and
returns `-1`. The final reference frees the child exactly once; both parent
allocations are also reclaimed.

The source uses Click's C0 declarations of `int32`, `malloc`, and `free`.
The target is the default x86-64 Linux LP64 profile with eight-bit bytes and
unsigned plain `char`. No source refactoring, alternate release entry point,
or proof-only C operation is used.

Native syntax-only smoke, supplying those declarations without editing C:

```sh
clang -std=c11 -Dint32=int -include stdlib.h \
  -Wall -Wextra -Werror -fsyntax-only design/shared-heap-probes/shared_parent.c
```

This compiler check establishes syntax only. Check the ownership proof with:

```sh
click verify design/shared-heap-probes/shared_parent.click
click audit design/shared-heap-probes/shared_parent.click
```

The embedded-source regression is
[`shared_heap_population_lifecycles.md`](../../mdtests/shared_heap_population_lifecycles.md).
Its two caller proofs preserve payload reads, both destruction orders,
allocation failures, and complete cleanup.

## Contracts and resources

`child_ref(obj)` is one reference in a population. Its empty body grants no
child-memory access. `child_control(obj)` owns the allocation, child object,
and `authority(child_ref(obj))`; its invariant ties `obj->refs` to the exact
population count. `child_storage(obj)` carries the same ownership before C
initialization, without asserting anything about uninitialized fields.
The creator establishes empty authority immediately after successful allocation.
Initialization borrows storage and produces the first reference.

A named `parent(p)` instance owns the link cell and records an `Empty` or
`Linked(kid)` model. Its reference remains a separately transferred companion
resource. The parent does not own another copy of child control: both parents
refer to the same population and helpers explicitly transfer the single
control resource as needed. Named parent fold/unfold uses the ordinary checked
memory exchange and does not change the population ledger.

Retain borrows control and a reference and produces another reference. Attach
uses that retain operation and produces a parent link. Payload reads borrow
control and a reference. Release consumes one reference and control, returning
control only when the old count exceeded one. Final release consumes empty
authority and frees the child. Detach uses the same conditional transfer,
naming the returned child by `old(p->kid)` because C clears the link.

All of these use existing `owns`, `consumes`, `produces`, `fold`, `unfold`,
and conditional clauses. Pointer aliases must resolve to the same checked
population; a parent-field spelling cannot create a second authority.

## Migration corrections

Three older detach fixtures borrowed one reference, consumed another, and
also promised an extra produced reference despite only decrementing the C
counter. `owns` already returns the borrowed survivor. The migrated contracts
remove that duplicate output, preserving the real surviving reference and
all payload claims. The entry-pointer handoff fixture instead conditionally
returns child control, retaining its intended conditional-output regression.

Some older caller fixtures also inferred an initial population of one merely
from holding one reference. Their creator-population assumption is now stated
explicitly as `requires count(child_ref(kid)) == 1`. Owning a fragment does
not establish the global total. External callers that retain an arbitrary
population instead state the counter's real overflow bound: one retain requires
`count(child_ref(kid)) < 2147483647`, and two successive retains require
`count(child_ref(kid)) < 2147483646`. These are C arithmetic preconditions,
not a restriction that every caller starts with one reference.

The final detach proof explicitly discharges the conditional payload claim:
when the old count is at most one, its `old(count(...)) > 1` premise is false.
This keeps the proof small under the same work limits when a preceding smart
tactic is expanded into simple steps.

The related negative fixtures still test missing references, a missing retain,
a wrong child, an incorrect count after the first detach, missing initialization
facts, and a leaked reference or allocation. Their C remains unchanged.

This probe uses exact unary populations and sequential control ownership;
field-bearing members, wildcard authority scopes, and mutex-held controls are
supported elsewhere but not exercised here.
