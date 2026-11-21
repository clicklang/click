# Pointer values: a Surface form for a pointer's parts

Status: superseded by `design/pointer-model.md` before implementation. Its decisions D1-D5 were approved on 2026-11-20.

## Problem

A kernel pointer (`Pointer` in `src/kernel/primitives.rs`) is more than an
address. Its identity (`Pointer::identity`) is:

| Part | Meaning |
| --- | --- |
| address | the location: a base and a byte offset |
| provenance | the object the pointer was formed to designate |
| type | the C pointer type it is viewed through (`int32 *`, `struct node *`, a function pointer) |
| volatile | whether the pointee is volatile |
| bounds | the subobject it designates (`SubobjectBounds`: start and width), when known |
| bounds owner | when the bounds are not known, the opaque read or object whose domain bounds it |

Two further parts are not part of identity: `const` and the object class
(`design/effective-types.md`).

Every Surface form that produces a pointer fixes provenance and bounds from
how it is written:

- a read (`p[i]`, `*p`, `at(point, place)`, `old(..)`, `load<T>(..)`,
  `exact(..)`) has the read as its provenance and bounds owner;
- `&place` has the place's object as provenance and the place's subobject as
  bounds;
- arithmetic (`p + k`, `byte_offset(p, n)`) and casts keep their operand's
  provenance and bounds.

`address(p)` and `same_object(p, q)` only relate pointers. No Surface form
states a pointer's parts directly.

So a kernel pointer whose provenance or bounds do not follow from any spelling
of its address has no Surface form. The raise-lower principle
(`docs/internals/raise-lower-principle.md`) requires one. Today the raiser
prints the nearest spelling. That spelling lowers to a different pointer, and
the raise-lower audit counts it as `differs`. The main known case is a pointer
read named at its version point whose provenance is the read at another state
(`design/exact-reads.md`, "The pointer provenance rule"). The others are:

- pointers the kernel builds from facts;
- joins whose arms disagree on provenance or bounds;
- integer-to-pointer conversions.

Removing the mix at two construction sites (on master `c7e6ad49d`) changed 114
`differs` facts but removed only 14 net: 64 removed, 50 added.

- Most of the removed facts came back in another form. For example, the
  address equation `address(at(<state A>, sq+8)) == address(sq+8)` became the
  complete pointer equation `at(<state A>, sq+8) == sq+8`, which still differs.
- 5 new `differs` appeared in `contains(..)` facts. There a pointer built at a
  remaining site raises to a read that lowers through a converted site.
- The real improvements were concentrated in a few claims, such as `f` (14)
  and `probe` (about 10).

Removing the mix site by site moves the mismatch instead of ending it:
whatever remains, or arises later, still needs a form. This form comes first.

## The form

```
pointer<T>(address: a, provenance: q, bounds: b)
```

- `T` is a pointer type, written as in a cast. A `volatile` pointee is part
  of `T`, as in C. So is `const`.
- `a`, `q` and `b` are pointer-valued expressions. The form takes one part
  from each:
  - from `a`, its address;
  - from `q`, its provenance;
  - from `b`, its bounds: known subobject bounds, root bounds, or an opaque
    bounds owner.
- `provenance:` defaults to `a`.
- `bounds:` defaults to `q`.

So `pointer<T>(address: a)` is `a` viewed as `T`, and `pointer<T>(address: a,
provenance: q)` is `a`'s location with `q`'s provenance and bounds.

Taking each part from an expression, rather than from a new syntax for
objects, bounds and owners, reuses forms that already raise. A provenance or
bounds owner is always an object root or a read. Both already have Surface
forms:

- `&x`;
- an allocation result;
- a read;
- `exact(place)`.

Subobject bounds are those of an `&s->f` or an array element. The form adds
nothing to say about those parts. It only says which expression each part
comes from.

### Examples

A pointer read named at its version point, whose provenance is the read at the
exact state:

```
pointer<int32 *>(address: at(<state A>, q->next), provenance: exact(q->next))
```

A pointer formed one past the end of `s->first`, which keeps `first`'s
bounds although its address equals `&s->second`'s:

```
pointer<int32 *>(address: &s->second, provenance: &s->first + 1)
```

## Meaning

- **Spec only.** The form is a value in specifications and proofs. It has no
  C counterpart and is rejected in C code.
- **No access.** It grants nothing. Reading through it needs a resource for
  the object its provenance designates, exactly as for any other pointer.
  Choosing a provenance cannot create a permission.
- **Equality.** `pointer<T>(..) == p` is complete pointer equality: every
  identity part. `address(pointer<T>(address: a, ..)) == address(a)` always
  holds. `same_object(pointer<T>(address: a, provenance: q), q)` holds when
  `q` has object provenance.
- **Kernel Click.** Lowering produces exactly the `Pointer` with those parts.
  It reads no facts, so it is fact-stable
  (`docs/internals/raise-lower-principle.md#lowering-is-fact-stable`).

## Raising

The raiser decides from the pointer's own parts, never by trying spellings
and comparing their lowering:

1. Raise the address to its spelling `a`, as today.
2. If the pointer's provenance, bounds and type are the ones `a` already
   carries, print `a`. That is the common case, and output does not change.
3. Otherwise print `pointer<T>(address: a, ..)`. Give `provenance:` when
   provenance differs from `a`'s, and `bounds:` when bounds differ from the
   provenance argument's. Raise each part from its retained origin: an object
   root to `&x` or the allocation, a read to its read form.

`load<T>` and `byte_offset` are Surface escape hatches the canonical renderer
avoids when a source place exists. `pointer<T>` is one too: it appears in
output only when step 2 does not apply. Each such appearance is a pointer
whose parts the shorter forms cannot express. The audit lists them, so each
one is a visible case to fix at its construction site or to accept.

## What it is not

- Not `load<T>`. That is a read of memory; this builds a value and reads
  nothing.
- Not a cast. `(T *) a` keeps `a`'s provenance and bounds; this can replace
  them.
- Not integer-to-pointer conversion. The address comes from a pointer
  expression, never from a `uint64`. A kernel pointer built from an integer
  raises through the conversion's existing form, if it has one.

## Steps

Each step is one PR, measured with the raise-lower audit and
`scripts/audit.sh fact-stability`.

1. **The Surface form.** Parse, validate, lower and print `pointer<T>(..)`.
   Add mdtests:
   - each part lowers from its argument;
   - the defaults;
   - equality is complete, while `address(..)` keeps only the address;
   - the form grants no access;
   - it is rejected in C code.

   No raiser change.
2. **Raise to it.** Add raising step 3 above. Re-run the audit. Pointer
   `differs` whose cause is provenance, bounds or type should become `same`.
   The appearances of `pointer<T>` in the report list the construction sites
   that still mix parts.
3. **One identity per pointer read.** Move every pointer read's
   construction onto one function that decides its identity (version point
   and cell), with provenance and bounds derived from the read, not stored
   by each caller. Today about 18 sites call `Pointer::from_read`. Step 2's
   report shows which ones mix parts. The program-point work
   (`docs/concepts/memory-model.md`) decides how that identity is recorded,
   so this step is coordinated with it.

## Decisions

D1-D5 are approved.

1. **D1. Name: `pointer`.** It sits naturally beside `load<T>`, `address(..)`
   and `same_object(..)`. Add it to `BUILTIN_CALL_FORMS`
   (`src/surface/validation/declaration_table.rs`), so a user function named
   `pointer` is rejected as `address` or `exact` would be. One fixture defines
   its own: `mdtests/marked_pointer_valued_calls_keep_their_element_width.md`
   declares `function pointer<T>(p: T*) -> T* { p }` as a generic identity.
   Step 1 renames that helper to `same<T>`. The test is about element widths
   through states, not the name, so the rename does not change it.
2. **D2. `bounds:` defaults to the provenance argument's bounds.** Then
   `pointer<T>(address: a, provenance: q)` is exactly `q` moved to `a`'s
   location. That is the only default that never changes a part the author
   did not name. Defaulting to the whole object would quietly widen a
   subobject pointer's bounds: `provenance: &s->first` would cover all of
   `*s`, the widening `design/pointer-subobject-bounds.md` exists to prevent.
   An author who wants the whole object says so, with `bounds: s`, `bounds: &x`
   or the allocation.
3. **D3. The object class comes from `provenance:`.** The class records the
   object the pointer was formed to designate, and it survives casts and
   arithmetic (`design/effective-types.md`), so it belongs with provenance.
   `T` only chooses the view, as a cast does. Taking the class from `T` would
   let a spec relabel an object's effective type by writing a different `T`.
   `const` follows `T`, as in C.
4. **D4. A function-pointer `T` takes `address:` only.** A function pointer
   has no object domain: `Pointer::from_read` and `from_point_read` return
   before setting provenance or bounds. So `pointer<T>(address: a)` with a
   function-pointer `T` is allowed, and is the cast. `provenance:` or
   `bounds:` with such a `T` is a validation error that names the reason. A
   function pointer's `address:` must itself be a function pointer, or the
   result would be a function pointer with object provenance.
5. **D5. No new syntax for projected states.** A projection is the memory one
   read was evaluated against. Its source state is recorded
   (`canonical_load_projection_source`). Raise a read at a projection as the
   read of the same place at its source's program point. That is the reading
   `design/exact-reads.md` ("States with no program point") already gives
   projections, and it is what direct lowering selects. A part whose read has
   no recorded source, or whose source has no program point, stays unraised,
   and the audit reports it. That gap belongs to the program-point work, which
   is the one place to close it, so this form adds nothing for it.
