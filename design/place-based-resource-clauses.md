# Place-based resource clauses

> ACCEPTED (2026-10-07), being implemented in the order given below. It
> records the problem, the rule, what each current spelling becomes, and the
> questions still open.

## The problem

A resource clause says which memory a function owns or views. Click has two
ways to say that, and the surface mixes them.

- **By address.** The clause takes a pointer and a count. `owns q[0..n]` is
  `n` cells starting at `q`. This is how the kernel holds a memory fact: a
  base pointer, a start, an end, and an element width.
- **By place.** The clause names a thing in the program. `owns a->n` is the
  field `n`. This is how the source language names storage.

Each oddity below is a seam between the two. All were checked against the
tool on 2026-10-07, with `struct arena { int *data; int n; }`,
`struct cell { int value; int other; }`, `int *q`, `struct cell *p`, a global
`struct cell g` and a global `int total`.

| Clause | Result today |
| --- | --- |
| `owns a->n;` | accepted |
| `owns &a->n;` | accepted; the same resource as `owns a->n` |
| `owns a->n[0..1];` | accepted; a different, narrower resource |
| `owns a->data;` | refused: "pointer field `data` requires an explicit range for its contents or `&` for its storage" |
| `owns &a->data;` | accepted: the slot holding the pointer |
| `owns a->data[0..k];` | accepted: `k` elements `data` points at |
| `owns q[0..1];` | accepted |
| `owns &q[0];` | accepted |
| `owns q[0];` | refused: "expected `[`" |
| `owns *q;` | refused |
| `owns total;` | refused: "expected `[`" |
| `owns &total;` | accepted |
| `owns g;` | refused: "whole-struct views require a declared resource" |
| `owns &g;` | accepted |
| `owns p;`, `owns *p;` | refused |
| `owns object(p);` | accepted: the whole struct; `object(&g)` and `object(p + 1)` are refused |
| `owns p[0..1];` | accepted: `p->value` only |
| `owns p[2..3];` | accepted: `p[1].value` |
| `owns p[1].value;` | refused: "segment base did not evaluate to a pointer" |

Three of these are more than spelling.

**A one-element range on a scalar field loses its padding.** A field's slot
runs to the next field's offset or the end of the struct, so that padding
belongs to the object (`resolve_struct_field_metadata` in
`src/surface/parser.rs`). `owns a->n` therefore holds cells `a[2..4]`.
`owns a->n[0..1]` treats the `int` as a one-element array and holds
`a[2..3]`. A caller holding one cannot call a function that requires the
other: "held `owns a[2..3]` does not cover `a[2..4]`".

**A range on a struct pointer counts four-byte `int` cells, not structs.** A
struct pointer has no element width of its own, so the range falls back to
`int` cells from the base. The cells are typed: for
`struct wide { long big; char tag; }`, `owns w[0..2]` covers the bytes of
`big`, and a read fails with "a 8-byte load at `w` did not fit the cell's
value".

**Diagnostics print cells.** A missing `owns a->n` is reported as
`owns a[2..4]`.

`object(p)` and `&` exist because the address grammar has no way to write the
places `*p` and "the field itself".

## How much there is

Counted in mdtests, examples, stdlib and integrations. The first six rows are
a text classification of `owns`, `views`, `consumes` and `produces` clauses;
the last is from a temporary trace in the parser at the point where a range
follows a struct-typed base.

| Form | Uses |
| --- | --- |
| `ptr[lo..hi]` | 1,735 |
| bare field, `a->b` | 1,059 |
| `&place` | 956 |
| `object(p)` | 733 |
| field with `[0..1]` | 76 |
| `&place[lo..hi]` | 55 |
| range on a struct-typed base | 68, in 38 files |

The 76 include pointer fields, where `[0..1]` is a real one-element range of
the pointee; the scalar ones are not separated.

## Proposed rule

A resource clause takes a place, or a range of places.

```
target := place
        | place "[" lo ".." hi "]"
```

- A **place** is anything the program can name as storage: a variable
  (`total`, `g`), a field (`a->n`, `g.value`), an element (`q[i]`,
  `p[i].value`), or a dereference (`*p`). The clause covers that object's
  whole storage, including the padding that belongs to it alone.
- A **range** `X[lo..hi]` is the places `X[lo]` through `X[hi - 1]`. `X` must
  be a pointer or an array, and each element has `X`'s element type. A range
  on a struct pointer counts structs. A range on an `int` is a type error.
- There is no `&`. A place already names storage; its address adds nothing.
- `*p` is the whole object `p` points at. `object(p)` is retired in its
  favour and keeps its generated alignment requirement.
- `p` alone, for a pointer, is the storage that holds the pointer.
  `owns a->next` is the slot in `a`; `owns *a->next` is the node behind it.
  Both are needed, so `owns p` cannot also mean the pointee. A pointer
  parameter's own slot is not visible to a caller, so `owns p` in a contract
  is refused with the suggestion `owns *p`.
- Diagnostics print places.

The same target grammar applies wherever a memory target is written: `owns`,
`views`, `consumes`, `produces`, a loop header, a resource body, and
`viewable(...)`, `memory(...)` and `separate(...)`.

The kernel representation does not change. The surface lowers a place to the
cells it occupies, as it does now for a bare field.

## What each current form becomes

| Today | Proposed | Change in meaning |
| --- | --- | --- |
| `owns a->n;` | unchanged | none |
| `owns &a->n;` | `owns a->n;` | none |
| `owns &a->data;` | `owns a->data;` | none; the bare form stops being refused |
| `owns a->data[0..k];` | unchanged | none |
| `owns a->n[0..1];` on a scalar | `owns a->n;` | gains the trailing padding, which is the intent |
| `owns q[0..n];` on a scalar pointer | unchanged | none |
| `owns &q[i];` | `owns q[i];` | none |
| `owns &total;`, `owns &total[0..1];` | `owns total;` | none |
| `owns &g;` | `owns g;` | none |
| `owns object(p);` | `owns *p;` | none |
| `owns p[lo..hi];` on a struct pointer | fields, `*p`, or a range counted in structs | **changes**: today cells, proposed structs |

Only the last row changes what an accepted clause means. Those are the 68
occurrences above, and they must be rewritten before the new rule is turned
on for them.

## C++ and Rust

C++ and Rust sidecars use the same clauses, written against a C-shaped
restatement of each signature. The rule has to give the right answer there
too, and three things need a decision.

**References are spelled as one-element ranges.** C++ `int& value` appears in
the sidecar as `int32* value` with `owns value[0..1];` and is read as
`value[0]` (`tests/fixtures/cpp-verification/branch-return`). A Rust `&mut T`
or `&T` parameter is the same. Decided: each language spells a place the way
that language does.

| Source | Whole object | Field |
| --- | --- | --- |
| C `struct cell *p` | `owns *p` | `owns p->value` |
| C++ `cell& c` | `owns c` | `owns c.value` |
| C++ `this` | `owns *this` | `owns this->value` |
| Rust `c: &mut Cell` | `owns *c` | `owns c.value` |
| Rust `&mut self` | `owns *self` | `owns self.value` |

A C++ reference names its referent, so there is no separate slot and `owns c`
is the object. This needs C++ and Rust sidecars to state signatures in the
source's own parameter names and types, not a C-shaped restatement. That is
its own step, after the C work.

**Slices carry a separate length.** Rust `bytes: &[u8]` is restated as
`const uint8* bytes, uint64 bytes_len`, and the clause is
`views bytes[0..(int32)(uint32)bytes_len];` (`examples/rust-byte-sum`). A
slice is one place whose length the reference carries. A place-based surface
can say `views *bytes;` or `views bytes[..];` for the whole slice and keep the
explicit range for a part of it. This is an addition, not a change to an
existing meaning.

**"Padding that belongs to it alone" is language-specific.**

- In C, a field's slot runs to the next field or the end of the struct.
- In C++, a derived class may place its own members in a base class's tail
  padding. Owning a base subobject must not cover bytes a derived member
  lives in, so a base subobject's extent is its data size, not its `sizeof`.
  The C++ fixtures already name base members by path
  (`views self->state.right.size`), so places exist there; the extent rule is
  what needs stating.
- In Rust, field order and padding under the default representation are the
  compiler's choice and can change between versions. A place-based surface
  suits this: the sidecar names `self.slot`, and the extent comes from the
  layout the importer was given. A cell range written by hand cannot be
  right across compiler versions.

Rust's types already say which parameters are borrowed shared, borrowed
exclusively, or moved. Deriving default `views`, `owns` and `consumes`
clauses from them is a separate question from how a clause is spelled, and is
not part of this proposal (`design/rust-resource-correspondence.md`).

## Viewing memory at another width

Some proofs read memory at a width other than its declared type, for example
a struct as bytes. Today that can happen through a range. Under this
proposal a range always has the element type of its base, so reading at
another width needs its own explicit form. This proposal does not design that
form. It needs an inventory of the proofs that rely on it first.

## Order of work

1. Accept the places that are refused today: `owns q[i]`, `owns total`,
   `owns g`, `owns *p`, `owns p[i].value`, and a bare pointer field as its
   storage. Nothing that verifies today changes.
2. Print places in diagnostics.
3. Rewrite the corpus: `&place` to the bare place, `object(p)` to `*p`, and a
   one-element range on a scalar to the bare place.
4. Refuse `&`, `object(...)`, and a range on a non-indexable place, each with
   the spelling to write.
5. Rewrite the 68 ranges on struct-typed bases, then make such a range count
   structs.

6. State C++ and Rust sidecar signatures in the source language's own terms
   and accept that language's place spellings.

Steps 1 and 2 stand alone. Step 5 is the only one that changes the meaning of
an accepted clause.

### Progress

- Done: steps 1, 3 and 4 for `&` and `object(p)`. Both are refused with the
  spelling to write, and every proof in the repository uses the new forms.
- Partly done: step 2. A clause's own spelling prints as a place. Facts the
  kernel reports still print cells: a missing `owns a->n` is still
  `owns a[2..4]`, and a local's storage is `&second[0..1]`.
- Not started: a one-element range on a scalar field (`a->n[0..1]`) is still
  accepted and still excludes padding; step 5; step 6.
- `views *p` outside a resource definition is still refused, as
  `views object(p)` was ("whole-struct views require a declared resource").
  `views g` for a global struct is accepted. That difference is older than
  this work and is not yet explained.

## Open questions

- Should a whole slice have a spelling, and which?
- What is the explicit form for viewing memory at another width, and how many
  proofs need it?
- Do resource bodies and `viewable(...)`, `memory(...)` and `separate(...)`
  move together with contract clauses, or after them?
