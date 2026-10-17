# Effective types: checking strict aliasing in the kernel

Status: approved 2026-10-16: the principle and the undecidable-position rule
in [Decisions](#decisions).
The maintainer chose a kernel check over a frontend refusal the same day. This is the
prerequisite for one optimization level per project with `-O2` as the default
([project configuration, decision 1](../issues/project-config.md#further-decisions)).

## The hole, as it exists on master

At `-O2` without `-fno-strict-aliasing`, GCC assumes that an object is
accessed only through a type compatible with its own, up to signedness and
qualifiers, or through a character type (C11 6.5p7). The kernel checks memory
accesses by width and scalar layout only, so master `ea081fe3` verifies both
of these:

| Probe | Source | Verifies today | Should be |
| --- | --- | --- | --- |
| rank | `long long read(long *p) { void *v = p; long long *q = v; return *q; }` | yes | refuse the load |
| struct | `struct a { int x; }; struct b { int y; };` then `pb->y` where `pb` came from a `struct a *` through `void *` | yes, with `result == pa->x` | refuse the load |
| narrow | `*(unsigned short *)(void *)int_ptr` | no: width mismatch | refuse (unchanged) |
| bytes | `*(const uint32_t *)(const void *)u8_buf` | no: reached as a missing 4-cell view | refuse with the aliasing reason |

Today this is not unsound. A project without an option profile passes no
`-O` flag, so GCC builds it at `-O0`, and the one optimizing profile requires
`-fno-strict-aliasing`. It becomes unsound when `-O2` becomes the default.

Direct `T *` to `U *` casts are already refused by the frontend. The hole is
the `void *` round trip. The kernel keeps the pointer unchanged across it, and
nothing compares the access type with the object afterwards.

## Principles

- **Separate from authority and extent.** Ownership, views and subobject
  extents stay as they are. The new check is independent: the type an access
  uses must be allowed for the object at that position.
- **Object types come from declarations and stores, not from addresses.** A
  declared object has an authoritative type. A pointer parameter carries the
  type its declaration promises. A heap cell gets its effective type from the
  store that wrote it (C11 6.5p6).
- **Partial knowledge is checked for consistency.** A pointer parameter's type
  says what is at its address, not what surrounds it. The check refuses only
  combinations that no layout could reconcile. This keeps `container_of` from
  a `struct list_head *` parameter verifying.
- **Specification reads stay unchecked.** Contracts read memory as values; only
  C accesses carry an access type.
- **Certificate checking covers it.** The check sits beside
  `subobject_access_refusal` in kernel load and store evaluation, so statement
  theorems re-check it when a certificate is checked. The certificate format
  does not change.

## Representation

- **Access class** (`src/kernel/effective_type.rs`, new): `Char`, `Bool`,
  `Short`, `Int`, `Long`, `LongLong`, `Float`, `Double`, `VoidPointer` and
  `Pointer(pointee)`. Signedness and qualifiers of a scalar are erased, which
  allows exactly what C11 6.5p7 allows for scalars. `Char` reads and writes
  anything. A pointer's class keeps its pointee type, including signedness,
  and erases only the pointee's qualifiers; `VoidPointer` aliases every
  pointer class.
- **Object type:** a scalar class, a struct or union (translation-unit-qualified
  tag, size, members by offset), or an array of an object type.
- **Built in the frontend** from `C0Type` and `C0StructLayout` next to
  `to_kernel_type`. `Long` and `LongLong` come from `LongRank`, which lowering
  erases today.
- **Object side:**
  - `CBlock.declared_scalar_type` becomes `declared_object`, filled for locals,
    globals, statics, string literals and aggregate temporaries;
  - a pointer value's qualifiers gain `object: (anchor, object type)`. It is
    not part of the value's identity, like `extent`, and survives casts,
    `void *`, arithmetic, copies and store-and-reload;
  - `CHeapMemory` gains effective types for written heap cells.
- **Access side:** `TypedLoad` and the store lvalue carry the access class.
  A member access carries the struct it goes through, as
  `(anchor = address - member offset, struct type)`.

## The check

An access of class `A` at position `o`, relative to an object of known type
`T` at the anchor, is allowed when:

1. `A` is `Char`; or
2. `T` places a scalar of class `A` at `o`, or a union there has a member of
   class `A`; and
3. for a member access through struct `S` at anchor `s`, `S` occurs as a
   subobject of `T` at `s`, or `T` occurs inside `S` (partial knowledge only).

An authoritative type must satisfy these exactly. A provenance type, such as
a parameter's, must only be consistent with them: positions outside every
known layout are allowed. Positions are constants or `k * element + c`
through `canonical_offset_term`. Cost is one block lookup plus a walk of the
layout's depth per access, with no scan of unrelated state.

## Decisions

The maintainer approved this section on 2026-10-16.

**Principle.** Click refuses every C access that C11 6.5p7 makes undefined,
except where GCC documents a defined meaning. This is the rule GCC's optimizer
may rely on at `-O2`, not merely what it exploits today. The
[GCC alias probes](#gcc-alias-probes) confirm that GCC 13.3 relies on it.

Consequences, which follow from the principle and need no separate choice:

- **Scalars.** An access class erases signedness and qualifiers, and `Char`
  (plain `char`, `signed char`, `unsigned char`, `int8`, `uint8`) reads and
  writes anything. `long` and `long long` are distinct.
- **Pointers.** A pointer class is its pointee type with the pointee's
  qualifiers erased: `int *` and `const int *` agree, `int *` and
  `unsigned *` do not, and `void *` is compatible with every pointer class.
- **Unions.** Reading a union member other than the one last written is
  allowed, as GCC documents. A union at a position admits every member's
  class.
- **Calls.** Click verifies each function separately, so an argument's known
  object type must be consistent with the parameter's declared pointee type,
  and a returned pointer's with the declared return type.
- **Heap.** Memory without a declared type takes its effective type from the
  store that wrote it (C11 6.5p6). `memcpy` copies effective types, `free`
  clears them, and fresh `malloc` and `calloc` memory has none, so the first
  access is allowed and sets it.

The one decision beyond the principle:

- **Undecidable positions over a non-uniform layout are refused.** An
  array of one scalar class needs no position. A struct with members of
  different classes needs the access's offset modulo the layout. When the
  kernel cannot decide it, the access is refused with the aliasing reason
  rather than allowed. GCC has no such rule; it is the conservative choice
  where Click's knowledge runs out.

**Optimizing builds keep `-fno-strict-aliasing`.** The maintainer decided
this on 2026-10-17, after step 3b. The check refuses the accesses it can
see, but heap cells written by a callee or copied by `memcpy` carry no
recorded effective type: the record holds only while a cell keeps the value
its store wrote, and a call leaves the cells it may write unknown. Closing
that would need effective types in contracts, new specification syntax and
kernel work for a small optimization gain. So the check catches 6.5p7 bugs,
and the `-O2` build does not rely on it.

**Staging.** Each step is one PR with regressions for the refused and the
allowed cases:

1. scalar and pointer classes, so `long` vs `long long` and `int` vs `long`
   are refused through `void *`, for declared objects and pointer parameters;
2. struct access paths, including the struct probe, union reads and
   `container_of`, then `int *` classes and local byte arrays;
3. heap effective types and the call boundary;
4. the project optimization level, `-O2` by default. The Linux profile then
   stops requiring `-fno-strict-overflow` and
   `-fno-delete-null-pointer-checks`, and the promise attributes are refused
   in every project. `-fno-strict-aliasing` stays (see
   [Decisions](#decisions)).

## Status

- **Step 1 (scalar and pointer classes):** done.
  - Accesses carry their class. Loads and stores whose kernel type erases it
    (`long`, `long long`, exact pointer types) get it from the C frontend's
    type; others get it from the kernel type. Assignments through `*p` and
    `p[i]` first carried no class and went unchecked; they now carry the
    class of the lvalue they write.
  - Pointer parameters carry their pointee class from entry. A pointer read
    from memory carries its lvalue's pointee class unless it already carries
    one.
  - Declared locals and local arrays record their class on their block.
  - Loops keep a pointer local's class across the abstract iteration, and
    refuse a back edge that changes it.
  - `int *` and `int **` carried no class, because the frontend spells
    struct pointers with them; step 2b separates them.
  - Globals are not covered yet. Local `int8` and `uint8` arrays, which the
    frontend also uses for arrays of structs, were covered in step 2b.
- **Step 2a (struct access paths):** done.
  - A struct class is the struct's tag with the classes it contains at any
    depth: scalar and pointer members, embedded structs' contents, and every
    member of a contained union. A struct-pointer member's pointee is
    identified by tag alone, which keeps self-referential structs finite.
  - A member access carries `Member(container, member class)`. On a struct
    object it requires the same struct, a struct embedding the container, or
    one the container embeds (`container_of`). On a scalar object it
    requires the member's class. A scalar or pointer access on a struct
    object requires a member of its class.
  - Struct-pointer parameters carry their struct; declared local structs
    record it on their block. A struct-pointer member's load carries its
    pointee's full class, so the loaded pointer designates a known struct.
  - Positions are not compared: the check accepts a member of the right
    class at the wrong offset. The undecidable-position rule waits for
    positional checking.
- **Step 2b (`int *` classes and local arrays):** done.
  - The parser, which knows whether a declaration names a struct, gives
    `int *` and `int **` their classes: on parameters' pointees, on
    declared locals, on struct members, and on loads and stores through a
    variable or member declared without a struct. A load through another
    expression of an ambiguous type stays unclassed.
  - A declared local `uint8_t` or `int8_t` array records `char`; a local
    array of structs records its struct.
- **Step 3a (call boundary):** done.
  - A call is refused when a pointer argument's known object class, from
    its block's declaration or the pointer, is one the parameter's pointee
    class cannot designate (`CAccessClass::may_designate`: the accesses
    through that pointee type, a struct pointee as a member access through
    its struct). The refusal is a contract failure, not undefined behavior:
    passing the pointer is defined, but the callee is verified accessing it
    through the parameter's type.
  - A return is refused on the same rule against the declared return
    type, and the caller's result carries the return type's pointee class.
- **Class sources in specifications:** done.
  - A Click declaration gives a pointer the class a C declaration of the same
    type would. This applies to a model (`spec enum`) field, the result of a
    Click function, and a theorem parameter declared `struct T*`. A symbolic
    value of a model field, such as a match binder or a case witness, carries
    its field's class. A Click function's opaque pointer result carries its
    declared return type's class. A theorem is checked apart from any
    translation unit, so a theorem parameter's struct is identified by its
    tag alone.
  - A pointer-to-integer cast keeps the source pointer's class on the
    address term, so decoding the integer restores it. The destination type
    of the decoding cast never supplies a class. Like a pointer value's class,
    the address term's class is not part of the term's identity: a classed
    and a bare spelling of one address are one term for fact lookup,
    rewriting and premise matching.
  - Generic type arguments (`List<struct T*>`), quantified pointer binders,
    and resource fields of C pointer type still carry no class.
- **Specification reads:** done.
  - A contract operand the kernel evaluates as a C expression, such as a
    resource argument or a memory operand, is evaluated under
    `SpecificationAccessScope`, and so is a C fragment of a specification
    proposition. Its loads skip the check. Before, such a load carried no
    access class, and the kernel's fallback gave it its kernel type's class:
    `((struct sized_node*)(void*)old)->size` as a resource argument read as
    `int` and was refused against the `struct rb_node` its parameter
    designates, which stopped `examples/rbtree-augmented` wherever a contract
    names a node's cached count.
- **Step 4 (project optimization level):** done, with one exception the
  maintainer approved on 2026-10-17. A project names `optimization`, `-O2` by
  default, and every C unit is prepared at it; the Linux profile no longer
  requires `-fno-strict-overflow` or `-fno-delete-null-pointer-checks`, and
  the promise attributes are refused at any optimizing level. An optimizing
  level still adds `-fno-strict-aliasing`, permanently (see
  [Decisions](#decisions)).
- **Globals:** done. A global scalar, array, struct or array of structs
  records its declared class on its block when the block is first created
  at a function's entry, as a local does; a struct pointer global's class
  names its struct by tag.
- **Step 3b (heap effective types):** done.
  - `CHeapMemory.effective_types` (`HeapEffectiveTypes`) records, for each
    heap cell at a constant offset that a classed C store wrote, its class
    and the value written. A member store records its struct; a character
    store, or one without a class, records nothing and drops what it
    overlapped. A store at a symbolic offset replaces its block's entries
    with its own, keyed by its exact address spelling, which a read
    confirms only at the same spelling; any constant-offset store to the
    block drops it. So a block holds constant entries or one symbolic one.
  - The store records its entry under its own store edge, as it records
    the bytes it initialized, so the memory history stays connected.
  - An entry counts only while the cell still holds that value, so havoc,
    joins, calls and writes the record does not see need not maintain it: an
    unconfirmed entry is ignored. Interface joins keep the record only where
    every arm agrees; substitution rewrites its addresses and values as it
    rewrites cells.
  - Reads are checked against a confirmed entry; writes are not, because a
    store gives the cell a new effective type.
  - Not covered: `memcpy`'s copying of effective types and a callee's
    stores, which leave no entry, and a computed-index cell read through a
    different spelling of its address.
  - `one_classed_heap_store_and_read_are_logarithmic_in_recorded_effective_types`
    measures one classed store and one checked read against up to 1024
    unrelated recorded entries: both stay constant.
- **`-fno-strict-aliasing`:** kept permanently; the maintainer decided on
  2026-10-17 (see [Decisions](#decisions)). The plan is complete.

## Validation

- The probes above become mdtests: refused for `rank`, `struct` and `bytes`,
  and allowed for character views, signedness variants, `const`, union reads,
  own-struct access and `container_of`.
- Existing coverage to rerun at every step: `mdtests/c_void_pointers.md`,
  `integer_pointers_of_either_signedness_read_the_same_bits.md`, the
  `byte_representation_*` and union mdtests, `c_pointer_cell_cast_store.md`,
  the Linux rbtree tests and the examples.
- A scaling regression in the style of the subobject-extent work, so the check
  stays linear in the accesses checked.

## GCC alias probes

Each function stores through `a`, then through `b`, then reloads through `a`.
`gcc -O2 -S` with GCC 13.3 folds the reload to a constant exactly when it
assumes the two pointer types do not alias.

```c
struct sa { int x; }; struct sb { int y; };
int rank(long *a, long long *b) { *a = 1; *b = 2; return *a; }          /* folded */
int sign(int *a, unsigned *b) { *a = 1; *b = 2; return *a; }            /* reloaded */
int structs(struct sa *a, struct sb *b) { a->x = 1; b->y = 2; return a->x; } /* folded */
int member_int(struct sa *a, int *b) { a->x = 1; *b = 2; return a->x; } /* reloaded */
int ptrs(int **a, long **b) { *a = 0; *b = (long *)8; return *a == 0; } /* folded */
int psign(int **a, unsigned **b) { *a = 0; *b = (unsigned *)8; return *a == 0; } /* folded */
int pconst(int **a, const int **b) { *a = 0; *b = (const int *)8; return *a == 0; } /* reloaded */
int pchar(int **a, char **b) { *a = 0; *b = (char *)8; return *a == 0; } /* folded */
int pstruct(struct sa **a, struct sb **b) { *a = 0; *b = (struct sb *)8; return *a == 0; } /* folded */
int ppp(int ***a, long ***b) { *a = 0; *b = (long **)8; return *a == 0; } /* folded */
int voidp(int **a, void **b) { *a = 0; *b = (void *)8; return *a == 0; } /* reloaded */
```
