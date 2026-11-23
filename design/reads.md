# Reads: one term for a value read from memory

Status: draft for review. Nothing here is implemented.

This design sits between two others. `design/point-named-reads.md` decides
*which version* a read names: one selector, `ProgramPoint::read_version`,
over the held value, the point indexes and the legacy walk. `design/pointer-model.md` decides what a
pointer *value* is: an address and a provenance, with the type on the term.
This design decides what a read *term* is, so that both have one thing to
name.

## Problem

A value read from memory is spelled four ways in the kernel today:

1. **`MachineTerm::MemoryLoad(point, address, LoadKind)`**, for integer reads.
   A real term: equality compares the point's read key, the address and the
   kind.
2. **`AddressBase::LoadedPointer(PointerLoadId)`**, for pointer reads. The id
   indexes a side table, `POINTER_LOAD_REGISTRY`, holding `(point, cell,
   value type)`. The read's meaning is outside the term, and its type is in its
   key, so reading one cell through `int *` and through `char *` gives two
   pointer values. That contradicts the pointer model, where the type belongs
   to the term and not to the value.
3. **Load variables**: reserved `Variable`s registered in `LOAD_VARIABLE_REGISTRY`
   with a defining equation, used for some integer reads and, as
   `FunctionSymbolic(var)`, for function-pointer reads. Another session is
   removing them.
4. **`Address::loaded_value(memory, cell)`**, a pointer read named by the
   memory state's unchanged-bytes source, and `named_pointer_read`, which maps
   a raw 64-bit `MemoryLoad` to a `LoadedPointer`.

The pointer read's side-table type does three jobs at once:

- **Identity**: it is hashed into `PointerLoadId`.
- **Store lookup**: `indexed_typed_version` matches only a store whose value
  has that exact type, so a store at another pointer type answers nothing.
- **Raising**: `LoadedPointerView::value_type` tells the raiser how to spell a
  nested read.

Changing one job changes all three, so each pointer step so far has had to
decide read identity from the pointer layer.

## The rule

> A read's identity is what determines its value: the version point, the cell,
> and, for an integer read, the `LoadKind` it is read at. Nothing else.

- **The cell** is the address and the width in bytes. A 4-byte read and an
  8-byte read at one address read different bytes, so they are different
  reads.
- **An integer read's `LoadKind`** is part of it. For 8-, 16-, 32- and 128-bit
  reads the kind is the format, width and signedness, because the format
  changes the value: the `int8` and `uint8` reads of one byte are -1 and 255.
  They stay two terms related by the sign cast, as `MachineTerm::memory_read`
  states (maintainer direction, 2026-10-30).
- **64-bit reads are the exception.** Signed and unsigned 64-bit reads share
  `LoadKind::Bits64`, a carrier of the bits, with signedness applied where
  the value is used (`docs/concepts/memory-model.md`: "Signed and unsigned
  64-bit reads share a version of the same 64 bits"). Their values differ
  (-1 and 2^64 - 1), so by this rule they would be two reads. This design
  keeps today's behavior and leaves the inconsistency as open question 4.
- **A pointer read's type** is not part of it, because the type does not
  change the value. One version point and one 8-byte cell are one pointer
  value, whatever pointer type reads it. The type belongs to the `Pointer`
  term that uses the read.
- **Exactness** (`exact(place)`) is part of the version point. An exact read
  is named by its reading point (`design/exact-reads.md`), so it is part of
  the identity only through that point. `PointerLoadId` hashes `is_exact_read`
  separately today; that goes.

This is the pointer model's rule, "types belong to terms, not values", applied
to reads. It explains why integers and pointers differ: an integer's format is
part of its value, a pointer's type is not.

## The terms

- **Integer reads** stay `MachineTerm::MemoryLoad(point, address, kind)`, built
  only by `MachineTerm::read_named` and `MachineTerm::memory_read`
  (`design/point-named-reads.md`, P0).
- **Pointer reads** become a structural address base,
  `AddressBase::Read(PointerRead { point, cell })`. The cell is 8 bytes, so it
  has no width. It is interned, like the other shared children, so equality
  and hashing stay cheap. It replaces `LoadedPointer(PointerLoadId)` and the
  registry. A pointer read's value is the `Pointer` whose address is
  `Read(..) + 0` and whose provenance is opaque, named by the same read
  (`Pointer::from_point_read`, unchanged in meaning).
- **Function-pointer reads** are pointer reads, and move from load variables
  (`FunctionSymbolic(var)`) to `AddressBase::Read`. No admitted fact holds a
  load variable today (census `report_load_variables_in_facts`, 6,024 C
  mdtests): they survive only as internal minting, defining facts and their
  registry. The scalar tail is removed after the program-point migration.
- **`Address::loaded_value(memory, cell)`** is a memory-named read
  (`ReadKey::Memory`). It goes when the legacy walk does
  (`point-named-reads.md`, plan step 4). Until then it builds the same
  `AddressBase::Read` with a legacy point.

## Store lookup

A read's value comes from the store that set its version (read-over-write).

- A pointer read is answered by the latest store to its 8-byte cell at its
  version, if that store wrote a pointer of the same category, object or
  function, of any type. The stored value keeps its own provenance and
  array object; the reading term keeps its own type. An object pointer's
  member bounds are bytes (`SubobjectBounds`), independent of the pointee
  type, so they stay valid through a read at another object-pointer type. A
  function-pointer read takes its call target from the store, so only a
  function-pointer store answers it; reading a function pointer's bytes as
  an object pointer, or the reverse, is not answered by the store.
- An integer read is answered by a store of the same cell and format, as
  today. A store of another format answers through the sign cast, as R-mem
  already does.
- A partial or overlapping store ends the version and answers nothing, as
  today.

So `indexed_typed_version` matches a pointer read on "a pointer store of the
same category to this cell", not on equal types. That is in the program-point
layer's selector path (`read_version` → `ordinary_typed_version`), in
`program_point.rs`; its owner agreed to the change and reviews it.

## Raising

A read raises from its derivation (`design/pointer-model.md`, "Raising is by
derivation"): `n->next`, `p[i]`, `at(point, place)`, `exact(place)`, or
`load<T>(address)` when nothing names the place.

- **An integer read** raises at its format, which its term carries.
- **A pointer read used as a value** raises at the type of the `Pointer` term
  that holds it.
- **A pointer read nested in an address**, as the inner read of
  `n->next->next`, has no term of its own to carry a type. It raises through
  its place: the field declaration (`n->next`), the static slot's declaration,
  or the parameter's declared type, which the raiser already uses. Because the
  type does not change the value, any of these names the same read; it is
  never a guess between different reads.
- **When no place names it**, it raises as `load<T *>(address)` at the type of
  the cell's effective-type object class, if the cell has one. Whether every
  such cell has one is open question 1.

## Migration

The order respects `point-named-reads.md`, which owns version selection.

1. **P0 there**: one integer read constructor, with a ratchet. No change here.
2. **Pointer reads by version point, not type.** Drop the value type from
   `PointerLoadId`'s key and registry. Match pointer stores on "any pointer"
   in `indexed_typed_version`. The raiser takes the type from the
   occurrence or the place. This is the smallest change that makes the rule
   hold, and it can land before step 3.
3. **`AddressBase::Read`.** Replace `LoadedPointer(PointerLoadId)` and the
   registry with the structural, interned base. Every user of
   `registered_pointer_load_point` reads the base instead.
4. **Function-pointer reads** move from load variables to `AddressBase::Read`.
   Load variables then remain only for scalar reads, removed after the
   program-point migration.
5. **`loaded_value`** goes with the legacy walk.

Each step is one PR, measured with the gate harnesses, the raise-lower audit,
and `click audit legacy-walk`.

## Design check

```text
Design check
- Part: Memory and checking (fast). No search is added.
- Why this part: every read is named and compared here.
- Fast: step 2 hashes one field fewer. The store lookup reads the same point
  index cell, keyed by the read's address, with a weaker match. Step 3
  replaces an id and side-table lookup with an interned base: equality and
  hashing stay O(1). Scaling: the existing read-identity and point-index
  scaling tests, plus one that grows the number of differently typed reads
  of one cell and checks that they intern to one base.
- Fact-stable: lowering reads no facts to name a read; the type moves from
  the read to the term that lowering already builds.
- Failure: a nested pointer read that no place names and whose cell has no
  effective type does not raise; the raise-lower audit reports it.
```

## Open questions

1. **Effective type of an unnamed cell.** A nested pointer read that no field,
   static slot or parameter names raises at its cell's effective-type object
   class. Does every such cell have one, and does a spec `load<T *>` at
   another pointer type pass effective-type checking? If not, those reads
   have no spelling, and that gap is the defect to fix.
2. **Interning cost.** `AddressBase::Read` holds a `ProgramPoint` and an
   `Address`. It must be interned so that addresses stay cheap to compare;
   confirm with the scaling tests before step 3.
3. **Exactness in identity.** Integer read equality already compares only
   `read_key()`, so an `Exact` and an `IndexedCell` selection of one point are
   one term. Pointer reads should match. Two consumers ask `is_exact_read()`
   for more than first selection, and both still choose a version:
   - substitution and term rewriting keep an exact read's point when they
     rewrite its address (`is_exact_read() && has_certified_read_view()`),
     where an indexed version is reselected;
   - `exact-reads.md` E3 makes a pointer read's provenance and bounds owner
     the same kind of read as its address. With one term per point this
     holds, but `Pointer::from_read` names an exact read by the
     unchanged-bytes source; check that it builds the same point as the
     version path where they coincide.
4. **64-bit signedness** (for the maintainer). `Bits64` makes the signed and
   unsigned 64-bit reads of a cell one term, while every other width keeps
   them two. Either 64-bit reads split into two kinds, as 128-bit reads are,
   or the rule says a read's kind is its bits and signedness is always at the
   use, which would reverse the 2026-10-30 direction for the other widths.
5. **Types on pointer terms.** `Pointer` carries its type outside identity
   (`pointer-model.md`, "Types belong to terms"). Whether it should carry one
   at all, or whether every type comes from the operation or declaration that
   uses the pointer (accesses, calls through a function pointer, declared
   locals, parameters and fields), is being decided with the maintainer. It
   does not change the read rule.
