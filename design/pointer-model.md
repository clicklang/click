# Pointer model: the language's abstract-machine pointer

Status: approved, with decisions 1-5 (2026-11-21). Not implemented. Supersedes
`design/pointer-values.md`.

## Principles

1. Use the names C and Rust use.
2. The kernel's pointer is the language's pointer: each rule is stated the
   way the language states it.
3. Choose the correct design over the compatible or expedient one.

## The model

### A pointer value is an address and a provenance

C's provenance model (TS 6010) and Rust both define a pointer value as an
**address** plus a **provenance**. The kernel's pointer value is exactly that.
There are three kinds:

| Kind | Value |
|---|---|
| object pointer | address, provenance |
| function pointer | the function |
| null | null (no provenance) |

**Provenance** records what the pointer was derived from. It determines the
pointer's **allocation**: the storage instance (C) or allocation (Rust) that
one creating event produced, such as a variable instance, a `malloc` or
`Box::new`, or a literal. Provenance is per language:

- **C:** the allocation, plus the **array object** the pointer was derived
  from. C defines arithmetic and subtraction only within one array object
  (C11 6.5.6p8-9), and a member array is an array object inside its
  allocation. Today's "subobject bounds" become this part of C provenance.
- **Rust:** the allocation. A borrow tag can be added later with Rust's
  aliasing model (`roadmap/unsafe-rust.md`).

A provenance whose creation the kernel did not see, such as a parameter or a
pointer loaded from memory, is opaque. It is named by where the pointer came
from, as `ExternalObject` and `LoadedPointer` names are today. Two opaque
provenances may or may not be the same allocation.

### Types belong to terms, not values

In C every expression and object has a type (C11 6.5p1, 6.2.5): `p` has type
`int *`, `(char *)p` has type `char *`, and `*p` reads an `int` because of
`p`'s type. The value a pointer expression denotes does not carry that type:
converting between object pointer types and back yields a pointer that
compares equal to the original (6.3.2.3p7), and TS 6010 and Cerberus model a
pointer value as an address and a provenance. Rust's `p as *const U` likewise
changes the static type and keeps the value.

So a kernel term keeps its type, as a C expression does, and the pointer
value it denotes is the address and provenance. `(int *)p` and `(void *)p`
are different terms denoting the same pointer value as `p`: a cast changes
the term's type, not the value, and `*p` takes its access type from `p`'s
type. Pointer equality and identity compare values, so they ignore the type;
an equality used to replace one term by another keeps the replaced term's
type. `const` and `volatile` qualify the lvalue type of an access, which each
access states (step 3a). Step 3c removed the type from `Pointer::identity`.

One conversion has a meaning of its own in C: converting to a character
pointer forms a view of the object's bytes (C11 6.3.2.3p7). In C provenance
that view's array object is the allocation's bytes, TS 6010's granularity,
not the member the operand was formed from. So `(char *)&s->f` keeps the
address and allocation but widens the array object. The conversion forms the
view whether written or implicit, and from any non-character type, including
`void *`. A conversion between character types keeps the existing view. GNU
C defines arithmetic on `void *` as character arithmetic, so it forms the same
view; Linux's `container_of` relies on it. Whether a conversion forms the view
depends on the operand's static type, which every conversion has, so the rule
needs no type on the value (`design/pointer-subobject-bounds.md`, D4 as
revised).

A second conversion has a meaning of its own: a pointer to a structure's
initial member, converted to a pointer to the structure, points to the
structure (C11 6.7.2.1p15). When the operand's array object is a member
starting at its address and narrower than the struct, the result's array
object is the struct. Whether a struct is there is the effective-type
question each access asks (C11 6.5p7). The kernel cannot yet tell an initial
member from any other member that starts its own array object, because C
provenance does not record the enclosing struct; recording it belongs with
step 3's array object. Effective types (`design/effective-types.md`) stay with the
allocation, which provenance names.

### Equality

- **Value equality**, written `p == q` in a specification, compares the whole
  value: address and provenance. `&s->first + 1` and `&s->second` have equal
  addresses but different provenance (different array objects), so they are
  different values, as the reference already says for contracts.
- **C's `==`** compares addresses. It is `address(p) == address(q)` in a
  specification, as today.
- **Rust's `==` on raw pointers** also compares addresses.

### The language rules, named as the languages name them

| Rule | Click |
|---|---|
| C relational comparison: same allocation (6.5.8p5) | `same_allocation(p, q)` |
| C subtraction: same array object (6.5.6p9) | `defined(q - p)` |
| Rust `offset_from`: same allocation | `same_allocation(p, q)` |
| integer form | `address(p)` |

`same_allocation(p, q)` replaces `same_object(p, q)`. It compares provenance,
not the address's object. Like the rules it states, it is false when either
pointer is null. It is a single kernel fact that lowering never breaks into
parts, so it raises to itself.

### Reads

A pointer read is named by its version point and its cell (address and
width). Its value's provenance is derived from the read: the read is the
provenance of the pointer it produces. Every read of a cell produces the same
pointer value, whatever pointer type it is read through, because the type
belongs to the access. This is the rule `design/exact-reads.md` and the
raise-lower principle already state for reads: "one version point has one
name".

### Raising is by derivation

Every pointer the kernel holds comes from a language operation, and is raised
as that operation:

| Derivation | Surface |
|---|---|
| parameter | `p` |
| read | `n->next`, `at(point, place)`, `old(..)`, `exact(..)`, `load<T*>(..)` |
| address of | `&x`, `&s->f` |
| arithmetic | `p + k`, `byte_offset(p, n)` |
| call result | `call(f, 0).result` |
| proof or model binder | its name, displaced with `byte_offset` |
| cast | `(T *) p` |
| null | `0` |

There is no general constructor for a pointer's parts. The only operations
that combine one pointer's address with another's provenance are the
languages' own:

- Rust's `q.with_addr(a)` (strict provenance);
- C's integer-to-pointer conversion, under C's provenance rules.

Each is added, under its language's name, when the corresponding source
construct is supported.

A pointer the raiser cannot spell from its derivation is a defect, either a
missing Surface form for a derivation or a construction no program performs,
and the raise-lower audit reports it. No new spelling is invented for it.

## What changes from today

| Today | This model |
|---|---|
| identity: address, provenance, bounds, bounds owner, type, `volatile` | address and provenance; C provenance includes the array object |
| `same_object`: same address object, lowered to a conjunction | `same_allocation`: same provenance, one kernel fact |
| a read's provenance set by each caller, sometimes another read (the version-point/exact mix) | provenance derived from the read |
| the raiser guesses a read's pointer type (`int32 *`) | the term's type, recorded where the read is made |
| `pointer<T>(address:, provenance:, bounds:)` proposed for raising | not needed; Rust `with_addr` and the C cast when supported |

## Plan

Each step is one PR, measured with the gate and the raise-lower audit.

1. **This design.**
2. **`same_allocation`.** Rename `same_object`, compare provenance, and keep
   it a single kernel fact. Migrate its uses and the reference. Independent of
   the other steps.
3. **Types and qualifiers off the pointer value.** Identity becomes address
   and provenance. Qualifiers move to accesses, the type stays on the term,
   and subobject bounds fold into C provenance. This is the largest kernel
   change: equality, the equality graph, effective types and the raiser all
   change.
   - 3a, step 1: every C load and store states the volatility of its lvalue's
     type (C11 6.7.3p7), which the frontend computes as it computes pointee
     `const`. The kernel still also reads the pointer value's flag. Over the
     gate corpus the access's flag never misses a volatility the value has;
     it adds one where the value lost it, in Linux's `__WRITE_ONCE`
     (`*(volatile typeof(x) *)&(x) = v`).
   - 3a, step 2: `volatile` leaves the pointer value. Pointer identity no
     longer includes it, and parameter binding, local stores, casts and
     `&` of a volatile object no longer record it on the value. An access is
     volatile exactly when its own lvalue type is.
   - 3a, step 3: `const` leaves the pointer value. Writing through a
     const-qualified lvalue and dropping `const` in a conversion are C
     constraint violations (C11 6.5.16.1, 6.3.2.3p2) that the C frontend
     and Clang reject before Click verifies; across the C mdtests no kernel
     refusal on a pointer value's `const` fires. Writing a `const` object
     stays undefined behaviour that the storage's read-only status refuses
     (C11 6.7.3p6). Declarations keep their qualifiers.
   - 3c: the type leaves pointer identity and the keys that mirror it.
     Comparisons no longer require equal types or retype both sides first,
     and a rewrite by a pointer equality keeps the replaced occurrence's
     type. A cast still builds a term of the target type.
   - 3b, step 1: a pointer's array object is one value, `ArrayObject`:
     the allocation, an opaque array object (named by where the pointer
     came from, or unnamed for a view that may not use that name's
     coverage), or a member, with the opaque array object it was selected
     from. It replaces the separate `bounds`, `bounds_known` and
     `bounds_owner` fields of `Pointer`, `SharedPointer` and `LValue`, and
     rules out bounds on an opaque array object. Identity is unchanged.
   - The e-graph already keeps the two parts as the model needs: a pointer
     node joins a provenance node and an array-object node, `same_allocation`
     merges only provenance, and pointer equality merges both. No change.
   - 3b, step 2: comparisons that read only part of a provenance compare it
     whole (`Pointer::same_provenance_as`). Known value equality required
     equal allocations, bounds and addresses but not the array object, so a
     `same_allocation` fact and equal addresses made a parameter equal to a
     block pointer though it may point into a member.
   - 3b, remaining: memory ranges' carriers.
4. **One identity per read**, with provenance derived from the read. This is
   coordinated with the program-point work, which names reads by program
   point.
5. **Raise by derivation.** Remove the raiser's type guess. Land the binder
   byte-offset case (`byte_offset(binder, n)`). Treat any pointer that cannot
   be raised as a defect.
6. **Language constructors** as their source constructs are supported:
   Rust's `with_addr` and exposed provenance (`roadmap/unsafe-rust.md`), and
   C's integer-to-pointer conversion.
7. **Documents.** Rewrite `docs/concepts/memory-model.md` ("Blocks and
   pointers") and the reference sections, and remove the superseded designs.

## Superseded or revised documents

| Document | Change |
|---|---|
| `design/pointer-values.md` | superseded by this design |
| `design/exact-reads.md`, "The pointer provenance rule" | superseded: provenance is derived from the read |
| `design/pointer-subobject-bounds.md` | recast as C provenance's array object |
| `design/pointer-integer-representations.md` | revise with decision 5 |
| `docs/concepts/memory-model.md`, "Blocks and pointers" | rewrite in step 7 |
| `docs/internals/equality-closure.md` | update with step 3 |
| `docs/reference/language/index.md`: `same_object`, pointer equality, `address` | update in steps 2 and 7 |
| `roadmap/raise-lower-principle.md`, complete-pointer equality items | update with step 3 |
| `roadmap/unsafe-rust.md` | consistent; it is this model's Rust half |

## Decisions

All five were approved as proposed.

1. **C provenance granularity.** Should C provenance record the array object
   (proposed), or only the allocation, as TS 6010 does, with C's array-object
   rule checked separately? Recording the array object follows the standard's
   wording ("elements of the same array object") and keeps today's subobject
   protections, including the member-array subtraction check. The TS
   deliberately left subobject provenance open, so recording it is the
   stricter reading.
2. **What specification `p == q` means.** Value equality (proposed), with
   `address(p) == address(q)` for C's `==`; or C's `==` itself. Value equality
   is what proofs need for substitution, and it matches today's contract
   behavior.
3. **Volatile.** `volatile` qualifies the access in C, so it leaves the value
   (proposed). A volatile access must then carry the qualifier from its lvalue
   type, as C's semantics does.
4. **Unknown provenance.** A parameter's or loaded pointer's provenance is an
   opaque name (proposed, as today), and two opaque names are not assumed
   equal or distinct. The alternative, a fresh unknown per use, cannot express
   "same as the parameter".
5. **Integer-to-pointer conversion in C.** Follow TS 6010's exposed
   provenance (PNVI-ae-udi), where the conversion takes the provenance of an
   exposed allocation at that address (proposed), or keep today's fresh opaque
   provenance (`design/pointer-integer-representations.md`). Exposed
   provenance is C's model; the fresh-provenance rule is an approximation.
