# A one-past scalar-member pointer can read its sibling

Soundness: unsound. Ordinary C verification accepts dereferencing the pointer
one past a scalar member to read its sibling, despite C11's one-element scalar
array rule. The program's accepted memory-safety/defined-behavior claim is false.
The fixed-baseline recovery audit reproduces this on master `325f9f604` and the
archived implementation `e3d84a785` without changing source or claims.

Priority: P1.

Allocation bounds, matching addresses, initialized typed cells and permission
to read the sibling do not make the original pointer designate that sibling.

## Progress

Phase A step 2 of the [subobject-extent design](../design/pointer-subobject-extents.md)
rejects the in-function variants: the original C and C++ reads, the pointer
local, formation past the one-past end, a stored and reloaded member pointer,
and a loop walking past a member array. The fixtures are
`mdtests/a_one_past_scalar_member_pointer_cannot_read_its_sibling.md` and its
siblings. Step 3 refuses passing a member pointer to a callee, or folding it
into a resource, whose clause claims more than the member
(`mdtests/a_member_pointer_cannot_be_passed_as_a_longer_range.md`). Still
accepted: reaching another object through address equality inside a callee,
or from a pointer loaded at function entry (Phase B).

The Phase B investigation also reproduced an integer escape: converting
`&pair->first` to `unsigned long` and back lets an element-one read reach the
sibling. The regression is
`mdtests/a_pointer_integer_round_trip_keeps_its_subobject.md`. The working
prototype now rejects it and retains valid direct and stored-word member reads.
A hidden complete-value record preserves the original pointer; mathematical
integer observations cannot supply that record. The
[integer representation notes](../design/pointer-integer-representations.md)
record the implementation and the approved cast-based contract/tag support. This is
still an unpublished prototype: the full Phase B compatibility and scaling
checks must pass before closing this bug.

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


## Transport audit

Using the isolated typing extraction on `b8f7a8ea1` (submitted in #926), the
following controls pass fresh, expanded, rewritten and retained checking:

| Source pattern | Required result | Observed result |
| --- | --- | --- |
| `*(&p->first + 0)` | Accept, result is `p->first` | Accept |
| `*(&p->second)` | Accept, result is `p->second` | Accept |
| Return `&p->first + 1` without dereferencing it | Accept formation; address equals `&p->second` | Accept |
| Copy `&p->first` to a local, add one, dereference | Reject | Incorrectly accept |
| Store `&p->first` in a pointer field, reload, add one, dereference | Reject | Incorrectly accept |
| Pass `&p->first + 1` to a modular reader | Reject | Incorrectly accept |
| Return `&p->first + 2` without dereferencing it | Reject formation | Incorrectly accept |

The local variant uses the original Pair contract above and this C body:

```c
int32 probe(struct Pair* p) {
    int32* q = &p->first;
    q = q + 1;
    return *q;
}
```

The pointer-field variant declares `struct Holder { int32* link; };` and uses:

```c
int32 probe(struct Pair* p, struct Holder* h) {
    h->link = &p->first;
    return *(h->link + 1);
}
```

Its sidecar additionally owns `h->link` and requires that its footprint is
separate from each Pair field; it views both Pair fields and asserts the result
is `p->second`. The modular variant is:

```c
int32 read(int32* p) { return *p; }
int32 probe(struct Pair* p) { return read(&p->first + 1); }
```

The reader's sidecar has `views *p; ensures result == *p;` and both bodies use
`execute(); simp();`. The caller views both Pair fields and asserts the result
is `p->second`. The false acceptance crosses the call boundary, so a fix limited
to checking a direct member-address expression is insufficient.

Ordinary C lowering converts a field into a typed load at its byte address;
the field-load occurrence ID is not a subobject domain. `CPointerValue` carries
address, type and access qualifiers, while arithmetic consults held memory
ranges or allocation bounds. The archived pointer model additionally has a
legacy fallback for absent designations, so transplanting its representation
alone does not close ordinary C. The repair must couple authenticated field and
array selection, complete-value transport, checked arithmetic/access, and
symbolic entry versus actual call admission, while preserving address comparison
and the legitimate controls above.

A separate `int32** slot` spelling with `return *(*slot + 1);` stops earlier at
`pointer operation has no known pointee type`. That unrelated refusal is not
credited as pointer-domain rejection and must not be used to claim storage
transport is sound.
