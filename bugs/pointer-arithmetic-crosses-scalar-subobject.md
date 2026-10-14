# A one-past scalar-member pointer can read its sibling

Soundness: unsound. Ordinary C verification accepts dereferencing the pointer
one past a scalar member to read its sibling, despite C11's one-element scalar
array rule. The program's accepted memory-safety/defined-behavior claim is false.
The fixed-baseline recovery audit reproduces this on master `325f9f604` and the
archived implementation `e3d84a785` without changing source or claims.

Priority: P1.

Allocation bounds, matching addresses, initialized typed cells and permission
to read the sibling do not make the original pointer designate that sibling.

## Reproduction

Save this as a Markdown proof and verify it with the ordinary C frontend:

```c filename=probe.c
struct Pair { int32 first; int32 second; };
int32 probe(struct Pair* p) { return *(&p->first + 1); }
```

```click
verifying "probe.c";
int32 probe(struct Pair* p) {
    views p->first;
    views p->second;
    ensures result == p->second;
} by { execute(); simp(); }
```

Both fixed master `325f9f604` and archive `e3d84a785` accept this proof. The
required behavior is rejection of its undefined dereference. C11 6.5.6p7-p8
treats a scalar non-array-element object as an array of one element for pointer
arithmetic; the one-past pointer cannot be dereferenced to read another member.

The [recovery audit](../design/object-model-recovery-audit.md) records revisions,
commands and outcomes. The
[archived investigation](https://github.com/lacker/click/blob/e3d84a785792c007da19d2f42d75b9e143372164/bugs/pointer-arithmetic-crosses-scalar-subobject.md)
contains earlier C++ probes and pointer-field countermodels. Its native repair
notes describe that branch, not a closure of this ordinary C defect.

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

