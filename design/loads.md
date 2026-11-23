# Pointers, loads and stores

Status: draft for review. Nothing here is implemented.

## Scope

Three things carry every C, C++ and Rust memory operation the kernel reasons
about:

| Thing | Kind | What it is |
|---|---|---|
| **pointer** | value term | an address and a provenance (`design/pointer-model.md`) |
| **load** | value term | the bytes of a cell at a version point |
| **store** | memory event | a recorded step that writes a cell's bytes |

Below them are program points, which say what a version point is and how
stores are recorded (`design/point-named-reads.md`, `design/exact-reads.md`).
This design defines loads and stores, and how pointers use them.

"Read" stays the general word for anything that observes state: a local, a
binder, a resource field, `old(..)`. A **load** is the specific operation on
memory, as in Click's `load<T>(address)`, MiniRust and LLVM. A **pointer load**
is a load decoded at a pointer type.

## Problem

A value loaded from memory has six encodings today, each with its own identity,
store lookup and raising:

1. `MachineTerm::MemoryLoad(point, address, LoadKind)`, with fourteen kinds:
   every integer width and signedness, `Bits64`, both floats and
   `Abstract(T)`.
2. `AlgebraicTermNode::MemoryLoad`, for specification values held in memory.
3. `KernelTermNode::MemoryLoad`, the shared mirror.
4. `AddressBase::LoadedPointer(PointerLoadId)`, for pointer loads, with
   `(point, cell, value type)` in a side table, `POINTER_LOAD_REGISTRY`. The
   type is in the key, so loading one cell through `int *` and through
   `char *` gives two pointer values, and a store at one pointer type does
   not answer a load at another.
5. Load variables (`LOAD_VARIABLE_REGISTRY`), for some integer loads and, as
   `FunctionSymbolic(var)`, for function-pointer loads. No admitted fact holds
   one (census `report_load_variables_in_facts`, 6,024 C mdtests).
6. `Address::loaded_value(memory, cell)`, a pointer load named by a memory
   state's unchanged-bytes source.

Each new type needs its own copy of this machinery, and each change to one
copy is a change of identity for the others.

## The model

C, C++ and Rust define a load the same way. An object's content is its
**object representation**, a sequence of bytes, and an access at type `T`
**interprets** those bytes as a `T` (C11 6.2.6; C++ [basic.types.general];
MiniRust's typed load: load bytes, then decode at `T` against `T`'s validity
invariant). Which `T` an access may use is restricted (C effective types, C++
strict aliasing, Rust validity), but the bytes do not depend on it.

So:

- **A load is bytes.** `Load { point, cell }`, where `cell` is an address and a
  size in bytes. Its identity is the version point and the cell, and nothing
  else.
- **A value is a decoding.** `decode<T>(load)` is the load's value at `T`. The
  type belongs to the decoding, never to the load.
- **A store writes bytes.** A store of a value `v` at type `T` writes
  `encode<T>(v)` to a cell of `sizeof(T)` bytes, and gives that cell a new
  version point.

The pointer model's rule, "types belong to terms, not values", is this rule
for pointers: one cell's bytes at one version point are one pointer value,
whatever pointer type decodes them.

## Generic reasoning

Everything about loads and stores that does not interpret bytes is written once,
on cells, for every type:

| Reasoning | Rule |
|---|---|
| version selection | `ProgramPoint::read_version` chooses the point a load names (`point-named-reads.md`) |
| identity | two loads are one term when their version points and cells are equal |
| read-over-write | a load of exactly the cell a store wrote, at that store's version, is the store's bytes; this is `read_version`'s held-value and indexed-write steps (`point-named-reads.md`, P1 steps 1 and 2), not a third mechanism |
| overlap | a store that writes part of a cell, or overlaps it, ends the cell's version and answers no load of it |
| framing | a store, call or loop step proven not to write a cell leaves its version unchanged |
| separation | whether two cells can overlap, from their addresses and provenance |
| permission | owning a byte range authorizes loads and stores within it (`MemoryRange`, already type-free) |

## Per-type reasoning

Each type contributes one entry, and nothing else:

| Entry | Meaning |
|---|---|
| `encode<T>` | the bytes a store of a `T` writes |
| `decode<T>` | the value bytes have at `T` |
| validity | when `decode<T>` is defined: initialized bytes; `bool` 0 or 1; a valid enum tag; a non-null, aligned reference |
| conversions | how two decodings of one load relate: sign casts between integer formats of one width, bit-casts between integer and float |
| access | which `T` a load or store through a given lvalue may use (C effective types, C++ strict aliasing) |

The rule that joins the two halves is generic:

> A load whose version is a store of `v` at `T`, of exactly the cell that store
> wrote, decodes at `T` to `v`.

At another type `U` it decodes to `decode<U>(encode<T>(v))`, which the
conversions entry relates to `v` where one exists (the 8-bit sign cast,
a float bit-cast) and which is otherwise just that term.

Conversions are rewrites in checking, keyed by the two formats: the equality
graph relates `decode<int8>(l)` and `decode<uint8>(l)` by the sign cast with
no fact for a proof to find, as the `int8`/`uint8` load equality is free
today. Lowering may build a decoding at each format, which depends only on
types and so is fact-stable; it never folds the conversion.

Every cross-format decoding raises (`docs/internals/raise-lower-principle.md`):

| Decoding | Surface |
|---|---|
| `decode<U>(encode<T>(v))`, integers of one width | the C conversion `(U) v`, exact at equal width |
| `decode<U>(encode<T>(v))`, integer and float of one width | a bit-cast form, to be added before floats join step 3b |
| a pointer's bytes decoded as an integer, or the reverse | not supported until abstract bytes (step 5) |

### Integers and floats

`decode<int8>` and `decode<uint8>` of one byte are -1 and 255 for `0xFF`; the
sign cast relates them. Signedness is therefore part of the decoding, not of
the load.

This resolves an inconsistency in the current kinds. Today 8-, 16-, 32- and
128-bit loads carry signedness in their `LoadKind`, so the `int8` and `uint8`
loads of a byte are two terms (maintainer direction, 2026-10-30, stated at
`MachineTerm::memory_read`), while signed and unsigned 64-bit loads share
`Bits64`, one term with signedness at the use
(`docs/concepts/memory-model.md`). Under this model every width is like
`Bits64`: one load, decoded at each format. The 2026-10-30 direction's
substance, that the two values are different terms related by the sign cast,
still holds: they are two decodings of one load.

### Pointers

`decode<T *>(load)` is the stored pointer, with its provenance and array
object. When no store answers the load, it is an opaque pointer whose address
base and provenance are both named by the load.

- Every object-pointer type decodes the same bytes to the same pointer value.
  A member's bounds are bytes (`SubobjectBounds`), independent of the pointee
  type, so they stay valid at any object-pointer type.
- A function-pointer load decodes to the function the store wrote. Decoding an
  object pointer's bytes as a function pointer, or the reverse, has no stored
  value to return.
- The pointer term's type is the type it was decoded at (see open question 2).

### Aggregates and abstract values

A struct is decoded member by member: each member is `decode<M>` of a
sub-cell. This is what lowering already does when it copies a struct field by
field; the model names it. `Abstract(T)` is the decoding of `sizeof(T)` bytes
at an abstract type, whose value the kernel treats as opaque.

## Terms

- **`Load { point, cell }`**, one Rust type, interned. It is the identity of
  every load, of every type. `point` is the selection, not a bare point id:
  identity is its `read_key()` (`Memory`, `Point` or `View`) and the cell, so
  a memory-named load is expressible until the legacy walk goes. Interning is
  keyed by `(read_key, cell)`, never by the whole `ProgramPoint`, whose
  `IndexedWrite` selection holds a derivation.
- **Integer and float values** are `decode<format>(load)`. Today that is
  `MachineTerm::MemoryLoad(point, address, kind)`, built only by
  `MachineTerm::read_named` and `MachineTerm::memory_read` (enforced by
  `build_support/read_construction.rs`). It becomes the load plus its format,
  and the ratchet extends to the new variant and to `Load { .. }` literals.
- **Pointer values** have address base `AddressBase::Load(load)`, replacing
  `LoadedPointer(PointerLoadId)` and the side table. A pointer-side
  constructor gets the same ratchet.
- **Function-pointer values** use the same base, replacing load variables.
- **`Address::loaded_value`** is a memory-named load (`ReadKey::Memory`); it
  goes with the legacy walk.

## Calls are stores

A call writes memory too. Its effect on a cell is a store event like any
other, recorded at the call's program point:

- a cell the contract does not let the callee write keeps its version (framing);
- a cell the contract states the exit value of is a store of that value, at the
  cell's type, at the call;
- a cell the callee may write without a stated value is a store of an unknown
  value, at the call;
- a result the contract states as an entry value, `result == old(*o)`, is the
  load of `*o` at the call's entry point, the same term the caller holds.

So `ensures *o == 0` answers a later load of `o` by read-over-write, and
`ensures result == old(*o)` makes the result the load the caller already has
facts about. Neither needs an equation that a proof must find.

- **The stored value comes from the contract's text**, never from facts
  admitted after the call: only an `ensures` conjunct of the shape
  `place == expr` stores `expr`. Every other shape is an unknown store. This
  keeps the term fact-stable, and in `point-named-reads.md` it is a new
  coverage slice of `read_version`'s step 2.
- **`old(*o)` is evaluated through `read_version` at the call's entry point.**
  If the caller's memory holds a value for `*o`, that value is the result:
  in acceptance case 1, `x`'s pointer, not a fresh load.

## Acceptance cases

The Rust `Box` work paused on cases where loads and stores lose precision at a
call (`Option::take` as a library contract,
`fn take<T>(o: &mut Option<T>) -> Option<T> { owns *o; ensures result ==
old(*o); ensures *o == None; }`). The C forms below are regressions for this
design:

1. **Entry value of a result.**
   `int32* take(int32** o) { owns *o; ensures result == old(*o); ensures *o == 0; }`;
   `p = make(); *p = x; o = p; t = take(&o); if (t == 0) return 0; v = *t;
   release(t); return v;` with `ensures result == x`. The `t == 0` branch must
   be decided: `t` is the caller's load of `o`, which is `p`, which is not null.
2. **Exit value of a place.** `t = take(&o); if (o != 0) return 0; release(t);
   return x;` The branch on `o` must be decided: the call stored 0 to `o`.
3. **Framing a symbolic-size cell across a call.** Rust generic-stack `pop`:
   `let node = self.head.take()?; self.head = node.next; Some(node.value)`, with
   `Node<T>` laid out symbolically. The load of `node.value` (size `sizeof(T)`,
   offset `offsetof(Node<T>, value)`) must cross the `take` call, which owns
   only `self.head`. Today the call-havoc step gives up on any non-constant
   extent (`resource_tracker/step_effect.rs`, `CallHavoc`), and the node's
   two pointer loads are different `LoadedPointer` ids equal only by fact.
   Framing on cells with symbolic sizes, and one load per cell, are what fix
   it. It is also a regression for `point-named-reads.md` P2: framing a
   symbolic-size cell across a call is where the legacy walk stops.

A store that is recorded must be found by every later load of the same cell
however its address is spelled: an earlier attempt to replace the call's havoc
with the stated store was unsound because the havoc range and a later load
spelled the cell differently, so the load saw the pre-call value. Stores and
loads compare cells by the same identity.

## Abstract bytes

A complete foundation needs bytes that are richer than bit patterns, as
MiniRust's are: each byte is uninitialized, or a value with an optional
fragment of a pointer's provenance.

- **Uninitialized** bytes make `decode<T>` undefined. Click detects
  uninitialized reads today with special cases; they become a validity check.
- **Provenance fragments** let a pointer copied byte by byte (`memcpy`, a
  `char *` loop) keep its provenance, and make loading a pointer's bytes as an
  integer the provenance-dropping case that C (TS 6010) and Rust (exposed
  provenance) both define.

This is the last stage. The earlier stages do not depend on it.

## Raising

A load raises from its derivation (`pointer-model.md`, "Raising is by
derivation"): `n->next`, `p[i]`, `at(point, place)`, `exact(place)`, or
`load<T>(address)` when no place names it. The type spelled is the decoding's.

- A value raises at the type it was decoded at.
- A pointer load nested in an address, such as the inner load of
  `n->next->next`, raises through its place: the field, static slot or
  parameter declaration names it. Any of them names the same load, because
  the type does not change it.
- A load that no place names raises as `load<T>(address)` at the cell's
  effective type. Whether every such cell has one is open question 3.

## Migration

Version selection stays with `point-named-reads.md` and its owner. Each step
is one PR, measured with the gate harnesses, the raise-lower audit and
`click audit legacy-walk`.

1. **Pointer loads by version point, not type.** Drop the value type from
   `PointerLoadId`'s key and registry. In `indexed_typed_version`, a pointer
   load matches a pointer store of the same category, object or function, of
   any type; the program-point session reviews this change to its file.
2. **`Load` and `AddressBase::Load`.** Introduce the interned `Load` and use it
   as the pointer base, replacing `LoadedPointer(PointerLoadId)` and the
   registry. Function-pointer loads move from load variables to it.
3. **Integer and float loads on `Load`**, in two PRs, with the program-point
   session, whose constructors and ratchet gate these terms. Neither overlaps
   that session's own read-identity changes (its P1 producer moves); the two
   are scheduled apart so that failures stay attributable.
   - **3a.** `MemoryLoad` becomes `Load` plus a kind, keeping the kind's
     signedness in the key. Neutral: both harnesses pass, and the
     mixed-name census and legacy-walk counts stay flat.
   - **3b.** One load per cell, decoded at each format; `Bits64` stops being
     special. The held-value and indexed lookups answer a load at another
     format of the same width, `decode<U>(encode<T>(v))`, where today they
     miss and fall to the legacy walk. This changes how terms print, so it is
     classified on its own.
4. **Algebraic and abstract loads** become decodings of `Load`.
5. **Abstract bytes**: uninitialized bytes and provenance fragments.
6. **`loaded_value`** and the remaining scalar load variables go with the
   legacy walk.

## Design check

```text
Design check
- Part: Memory and checking (fast). No search is added.
- Why this part: every load is named, compared and answered here.
- Fast: a load's identity is an interned (point, cell): equality and hashing
  are O(1), as the side-table id is today. Store lookup reads the same
  point-index cell, keyed by the load's address, with a match on store
  category instead of type. Decoding is a per-type function of one load.
  Scaling: the existing load-identity and point-index scaling tests, plus
  one that grows the number of differently typed decodings of one cell and
  checks that they share one `Load`.
- Fact-stable: lowering names a load from its version point and cell; the
  type moves to the decoding lowering already builds. No fact is read.
- Failure: a nested pointer load that no place names, at a cell with no
  effective type, does not raise; the raise-lower audit reports it.
```

## Open questions

1. **Signedness of a load.** This design makes every integer load one load,
   decoded at each format, as `Bits64` is today. That keeps the 2026-10-30
   direction's distinct terms as distinct decodings. Confirm that this, and
   not two loads, is the intended reading.
2. **Types on pointer terms.** `Pointer` carries its type outside its identity.
   Whether it should, or whether every type comes from the operation or
   declaration that uses the pointer, is being decided separately. It does not
   change loads.
3. **Effective type of an unnamed cell.** Does every cell that no place names
   have an effective type that a specification `load<T *>` can use, and does
   effective-type checking accept a load at another pointer type? If not,
   those loads have no spelling, and that is the defect to fix.
4. **Exactness.** Integer load equality compares only `read_key()`, so an
   `Exact` and an `IndexedCell` selection of one point are one term; pointer
   loads match. Substitution and rewriting keep an exact load's point when
   they rewrite its address, and `exact-reads.md` E3 makes a pointer load's
   provenance the same kind of load as its address. `Pointer::from_read`
   names an exact load by the unchanged-bytes source, a memory-named key;
   where it coincides with a version-path load that is a mixed name, the
   pointer form of the 53 integer cases. The mixed-name census
   (`kernel::mixed_read_names`) extends to pointer loads once step 2 gives
   them one constructor.
5. **Interning cost** of `Load`, confirmed by the scaling tests before step 2.
