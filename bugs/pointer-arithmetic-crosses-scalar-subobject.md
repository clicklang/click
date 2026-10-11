# A one-past scalar-member pointer can read its sibling

The shared evaluator accepts a C++ and C program that dereferences the pointer
one past a scalar record member to read the following member. Both probes
verified locally during the object-model audit at `8153b3ac0`.

This is a soundness defect, not missing proof automation. Allocation bounds,
matching addresses, initialized typed cells and permission to read the sibling
do not make the original pointer designate that sibling.

## Reproduction

Save the following as a Markdown proof and run `click verify PATH.md` with the
pinned C++ exporter configured. The current result is `1 selected proof verified`.
The required behavior is rejection of the program's undefined dereference.

```cpp filename=pair.cpp function=probe profile=normal_only
struct Pair { int first; int second; };
int probe(Pair& pair) noexcept { return *(&pair.first + 1); }
```

```click
verifying "pair.cpp";
int32 probe(struct Pair& pair) {
    views pair.first;
    views pair.second;
    ensures result == pair.second;
} by { execute(); simp(); }
```

The C probe also verifies: use a `c filename=pair.c` fence with the same record
and `int probe(struct Pair* pair) { return *(&pair->first + 1); }`, then a
sidecar with `struct Pair* pair` and `pair->first` / `pair->second`.

A second C++ probe also verifies: change the function to return `int*` with
`return &pair.first + 2;`, change the contract result type to `int32*`, and use
`ensures 1 == 1;`. Here pointer formation itself exceeds the scalar member's
one-element domain. No dereference or strong result claim is needed to expose
the missing check.

## Source rule and affected boundary

C++20 N4861 [basic.compound] treats a scalar non-array-element object as an
array of one element for pointer arithmetic. A pointer past its end does not
point to a different object at the same address. [expr.add] permits formation
of the one-past pointer, not dereference of it. C11 6.5.6p7-p8 has the
corresponding one-element-array and one-past restrictions.

`CPointerValue` carries a block/offset address and access type, but no retained
object/array designation. C++ member-address lowering checks the member's
address, then common pointer arithmetic uses held ranges/allocation bounds.
The subsequent load can find the sibling's typed cell at the resulting address.
`src/kernel/eval/operators.rs`, `src/kernel/eval/memory_loads.rs` and
`src/languages/cpp/lowering.rs` are the relevant paths.

## Acceptance

- Reject the original C and C++ probes, including equivalent forms through a
  pointer local, stored/reloaded pointer, or modular helper. Do not merely match
  the syntax `&field + 1`.
- Reject formation beyond the selected domain's one-past endpoint even when
  the address lies within the enclosing allocation and the contract is trivial.
- Preserve valid scalar-pointer `+ 0`, formation/comparison of one-past pointers
  where the source language permits them, actual array traversal, and direct
  access through `&pair.second`.
- Keep memory aliasing/address equality distinct from typed access validity.
  A pointer comparison or equality rewrite must not upgrade a one-past pointer
  into a dereferenceable sibling pointer.
- Preserve pointer designation through value copying, calls, snapshots and
  supported pointer representation copies. Check the same rules during ordinary,
  expanded and retained verification, with local indexed work.
- Audit C, C++ and Rust lowering against the common rule; do not infer that a
  safe-Rust borrow justifies arbitrary raw-pointer arithmetic.

The [object-model design](../design/cpp-object-model.md#pointer-designation-a-confirmed-shared-gap)
records the required semantic boundary. Byte/word representation work must not
conceal this independent gap.
