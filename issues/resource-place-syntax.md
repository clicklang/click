# P1: Finish place-based resource clauses

Priority: P1.

Soundness: not soundness. The remaining work changes how accepted clauses are
spelled and how diagnostics print them. No false acceptance is involved.

## Goal

Every resource clause and every diagnostic names memory by its place in the
program (`p->field`, `*p`, `q[i]`, `p->data[lo..hi]`, a global's name), never
by raw cells. The accepted design is
[place-based resource clauses](../design/place-based-resource-clauses.md).
This item came from design-review M5 ("aliasing and place syntax are
inconsistent").

## Done

The design's steps 1 to 5 have landed, and so has step 6 for C++ reference
parameters and Rust contracts. Diagnostics (step 2) name memory as a place
for parameters' fields, elements behind a pointer field, one element of a
scalar pointer, a named object, an element or sub-range of an array field,
and memory reached through a chain of pointer fields (`h->in->a[i]`,
`o->b->data[i]`); a "covers only when" note inside an array field compares
indices of that field. A range that spans several fields of a struct has no
single place and is still described by byte offsets from its pointer. `&place`, `object(p)` and a range on
a scalar field are refused with the spelling to write. `owns a->n` is the only
spelling of that field. A range on a struct pointer counts structs. The
documentation states that a contract's `owns` clauses are disjoint from each
other and from its `views` clauses.

## Remaining

- **C++ struct reference locals (design step 6).** A scalar reference local
  reads in a proof as a reference parameter does. A struct reference local
  waits on the C++ importer admitting one; see [cpp-support.md](cpp-support.md).

## Intended regression

Done for diagnostics:
`a_missing_array_field_element_prints_as_its_place.md`,
`a_missing_array_field_element_through_a_pointer_chain_prints_as_its_place.md`
and `a_missing_element_behind_a_pointer_chain_prints_as_its_place.md`. A C++
mdtest with a struct reference local
whose proof reads a field through it as `r.field`.

## Acceptance criteria

- No refusal or note prints `owns a[lo..hi]` cells for memory that has a place
  spelling. A gate test checks the printed form on each kind of place.
- A C++ struct reference local can be named in a proof, or is refused by name
  with the spelling to use.
- `design/place-based-resource-clauses.md` records every step as done.
