# P2: Shared aggregate construction and return destinations

## Goal and invariant

Represent construction, copying and object lifetime explicitly in the shared
checked engine. A frontend must select the operation justified by its imported
language semantics. Constructing into a destination preserves that object's
identity; copying an existing aggregate preserves its field values, including
pointer values. Neither operation invents pointee authority or extends another
allocation's lifetime.

The shared constructor path already accepts an explicit destination. Existing
source frontends materialize aggregate returns as field copies into caller-visible storage.
That is not a general implementation of C++ returned construction: a constructor
can observe its object's address or store a pointer to one of its fields. An
extra copy can change the relationship between that pointer and the result
object. The unsupported C++ cases remain refused; this is a design gap, not a
claim that the currently admitted profile accepts an incorrect construction.

The chosen direction is to extend shared destination construction through
returns and temporaries, rather than requiring every admitted constructor to
be address-independent. Keep the existing allocation, layout, initialization,
resource and lifetime machinery. C and Rust retain their current source
semantics while C++ adopts the additional capability.

## Current foundation

- Shared `DeclareAggregate`, construction declarations and `CopyAggregate`
  already distinguish fresh storage from field copying.
- C, Rust and C++ use the shared aggregate-return layout interface. Rust also
  uses construction declarations with its existing move/drop and initialization
  protocol; changing return handling must preserve that protocol.
- C++ int32 field addresses follow checked nominal projections, preserve
  effective const qualification and check storage without reading field values.
- Existing offline regressions in [cpp_import.rs](../tests/cpp_import.rs)
  distinguish constructor identity from copying, exercise address formation
  before initialization, and reject missing write authority, false claims and
  forged const qualification.

The return materializer and symbolic call result live in
[functions.rs](../src/kernel/functions.rs); shared function interfaces live in
[contracts.rs](../src/kernel/primitives/contracts.rs). Investigate both concrete
execution and modular proof execution before selecting the new interface.

## Small intended regressions

Use this identity-sensitive class as the starting example:

```cpp
struct Node {
    int* self;
    int value;
    explicit Node(int input) noexcept : self(&value), value(input) {}
};
```

Direct construction of a local `Node node(input)` must establish
`node.self == &node.value` and allow a later read through `node.self` under the
object's existing authority. Forming the address before `value` is initialized
must not read the unwritten value. The source regression is already implemented
as `constructor_destination_preserves_pointer_to_its_own_field_offline`.

Copying a live `Node` into another object must retain the original self-pointer,
rather than rebase it to the destination field. This is already covered by
`record_copy_keeps_self_pointer_value_without_rebasing_it`.

Next add shared-kernel regressions for a constructor populating a supplied return
destination, forwarding that destination through another call, and constructing
a full-expression temporary followed by an explicit copy. Verify object
identity, initialized fields and the exact surviving storage at each boundary.
Reject reads through pointers into retired temporary storage.

Only then admit corresponding unchanged C++ factory/caller source. For example,
`return Node(input)` must follow the selected language/compiler profile's actual
construction and permitted copy rules. Do not assert a universal self-pointer
identity for every trivially copyable returned class: required prvalue
construction, optional named return elision and permitted trivial-class
parameter/result temporaries must be distinguished. Keep cases refused while
that evidence or their checked transitions are missing.

## Design work and delivery order

1. Specify destination identity, initialization state, result binding and
   lifetime in the shared call/contract interface. Identify how ordinary
   execution, modular calls and checked proof objects represent the same
   transition. A caller-provided destination is not automatically fresh or
   distinct from arguments and other caller storage.
2. Implement checked construction into result storage and destination
   forwarding. Preserve field-copy returns as an explicit existing operation.
   Complete initialization must be proved before a value can be observed;
   exposing an address grants no extra read or write permission.
3. Represent temporary materialization and retirement at the correct boundary.
   Keep descriptor storage separate from the backing allocations to which its
   pointer fields refer. Copying or retiring a descriptor must not retire those
   independently live allocations.
4. Admit a bounded C++ source profile using Clang's resolved expression
   categories, constructors, copy operations and compiler/ABI evidence. Account
   for every admitted execution instead of selecting an elision silently.
5. Verify unchanged pinned `std::span<int>` returned construction and complete
   the `SpanPopBack` target in [cpp-support.md](cpp-support.md). Keep the existing
   native reference contracts, uint64 extent and accepted single-range bound.

The accepted interface direction, Surface Click boundary, initialization and
lifetime obligations, and staged implementation contract are recorded in
[the aggregate construction design](../design/aggregate-construction.md).
The shared kernel now supports complete-object destination returns, including
body execution and body-certified summaries forwarded through two factories.
The hidden result binding grants no storage or ownership; actual writes must
initialize the modeled value fields. Existing C/Rust copy returns are unchanged.
Ordinary void constructors now bind an explicit destination parameter and
complete its initialized fields through body-certified summaries, including
aligned subobjects without resizing their parent allocation. Constructor proof
entries describe an unwritten footprint without fixing the parent's extent.
C++ local construction uses raw storage and explicit embedded constructor calls,
while the shared lifetime-end statement covers
temporary retirement. Returned-construction source admission and expression
lifetime lowering remain to be connected.
The precise compiler/ABI evidence is an admission gate for each new C++ return
shape; the design does not treat a Clang expression category as sufficient
evidence of copy elision.

## Acceptance criteria

- Direct construction, explicit copying, forwarding and temporary retirement
  have distinct checked transitions with stable allocation identity and correct
  initialized-field state. No blanket elision or pointer rebasing rule is added.
- Missing initialization, authority or lifetime evidence, incompatible layouts,
  forged destination identities and unjustified separation are rejected. Include
  caller destinations aliasing arguments and partial-construction failures.
- Native C++ result signatures and field/reference contracts remain usable;
  generated certificates accurately represent the selected storage transitions.
- Ordinary verification, expansion/reverification and retained verification
  agree for the positive and negative kernel and imported-source regressions.
- Existing C aggregate return/copy proofs and Rust construction, aggregate
  return, move/drop and scope-exit proofs retain their behavior. Frontend
  interface updates are limited to what the shared design requires.
- Unchanged pinned span construction and `SpanPopBack` verify within their
  documented profile, including descriptor/backing separation, returned-reference
  validity and preservation of caller backing authority.
- Any changed verifier hot path has relevant deterministic scaling checks;
  no unrelated-fact scan, increased search budget or source rewrite substitutes
  for the required evidence.

General ownership, arbitrary nontrivial class values, broad destructor/unwind
support, Rust pinning, ABI coverage beyond the selected profile and a redesign
of all object lifetimes are separate scope. C-prefixed shared kernel names do
not require a repository-wide rename as part of this work.
