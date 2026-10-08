# Design review of the proof language: open items

Priority: P2.

This is the one list of what the 2026-10 design review of Click's surface
language left open. Defects with a reproduction are in `bugs/`; everything
else from the review is here. Add to this file; do not open a separate issue
for a review item. Delete an item when its change, regression and
documentation land, and delete the file when it is empty.

Each item says what is true today, what was decided or is still to decide,
and what done means. "Decide" marks an item that needs the maintainer's
choice before any code.

## Violated invariant

One thing has one spelling, and a spelling means the same thing wherever it
appears. Each item below is a place where the language has two spellings for
one thing, one spelling for two things, or a form that is accepted in one
position and refused in another without a reason a user could give.

## A. Resource clauses name places

Design and progress: `design/place-based-resource-clauses.md`. Steps 1 to 5
are done. These remain.

### A1. Referents in printed kernel terms

C++ reference parameters are done: a sidecar declares `int32& value`, the
name is the referent, `&value` is its address, and the pointer that carries
it is named `&value` throughout (`reference_carrier_name` in
`src/languages/c/syntax.rs`; design section "Reference parameters"). A
member function's receiver is the pointer `this`.

A fact or a failed goal about a referent prints it as the sidecar writes
it: `value`, `owns value`, and `box.first` for a read at the start of a
struct referent.

One printing gap remains. The "C operation" line of a failure, and a
condition `click expand` writes from a lowered C expression, print
`load_int32(&value)`. That parses back correctly, but it is not what a
sidecar writes. The printer there has no parameter list, and the same shape
through a struct reference, `load_int64(&box)`, is the struct's first field,
not the struct. Lowering a scalar referent's read as an index of its carrier
would let the printer tell the two apart; it changes the lowered program and
the tests that pin its shape.

Regression: `click expand` on a branch over a scalar reference writes the
condition with the bare name, and on a branch over a struct reference's
first field writes `box.field`.

Done when: no diagnostic or expansion prints `load_...(&name)` for a
reference parameter.

### A3. Reference locals in C++ bodies

Not actionable today. The C++ importer does not lower a local of reference
type: `int& r = x;` is refused with "C++ local `r` has an initializer
outside direct lowering" (`lower_statement` in
`src/languages/cpp/lowering.rs` lowers scalar locals and records only). So
no proof can name one yet.

When the importer learns to lower one, it names the carrying pointer `&r`,
as `reference_carrier_name` does for a parameter, so that a proof reads `r`
as the referent with no further change.

Regression, for that change: a function with `int& r = x; r = 1;` whose
proof states `have r == 1;` and whose expansion re-verifies.

### A4. Rust sidecars in Rust syntax

Decided 2026-10-08: a Rust sidecar states its signature in Rust syntax, and
each language spells a place its own way, so a Rust `c: &mut Cell` is
`owns *c` and `c.value`. Not designed. Today the sidecar restates signatures
in C shape (`const uint8* bytes, uint64 bytes_len` for `bytes: &[u8]`), a
slice carries its length as a second parameter, tuple fields are `_0`, and
layout is the compiler's.

Next step: a proposal under `design/` covering the signature grammar, how a
slice and its length are named, the spelling for a whole slice (today only
`views bytes[0..(int32)(uint32)bytes_len]`), tuple and enum fields, and the
migration of the hash-pinned sidecars under `design/charon-trial`.

## B. Contracts and resource declarations

Found in the third pass and ruled on 2026-10-07. Each was checked against the
tool that day unless it says otherwise.

### B1. A child with fields in a resource without fields

A resource holds a child resource with `owns inner(p);`, the clause it uses
for memory; `contains inner(p);` is retired and refused with that spelling.

A child can also be named, `owns item: inner(p);`, so the parent's facts can
read the child's fields as `item.field`. That is accepted only in a parent
that declares fields of its own, because the parent's model is where the
child's model is kept. In a parent without fields it is refused: "this
resource declares no fields to hold them; write the child without a name".

Decided 2026-10-08: it should be allowed. Today a resource without fields
cannot hold a child that has fields at all, and the two refusals point at
each other: the unnamed form `owns counted(p->a);` is refused with "resource
`counted` has fields; bind it with `owns name: counted(...);`".

Intended reading: the parent does not keep the child's fields. Holding the
parent means some values of the child's fields exist for which the child is
held and the parent's facts are true; unfolding gives the child with fresh
values and those facts. A parent that needs a value tracked across a fold
declares a field for it. The parent stays fieldless and is held without a
name. Not yet checked against how the kernel unfolds and folds a resource
without fields; if this reading does not fit, report what does before
building another.

Regression: `resource pair(p) { owns p->n; owns first: counted(p->a); fact
p->n == first.v; }` with no field in `pair`, folded and unfolded, with a
claim that follows from the fact verifying and one that needs the lost value
refused; the unnamed form accepted.

### B3. Reads go through an owned resource: the loop case

Decided 2026-10-08 and built: holding a resource, viewed or owned, lets C
read the memory it owns directly. A write still needs `unfold`. Depth stays
at one level: memory a child resource owns is not read through.
`mdtests/c_reads_through_an_owned_resource.md`,
`c_does_not_write_through_an_owned_resource.md` and
`an_owned_resource_unfolds_after_a_read_through_it.md` pin the rule.

What remains is that it is built two ways (`OwnedCores` in
`src/surface/proof/resources.rs`):

- In a function with no loop, the views of an owned resource's memory are
  attached to the owner's occurrence, so they retire when the owner is
  unfolded, consumed, freed or handed to an interface.
- In a function with a loop, they are free-standing views, as before the
  decision. A loop head gives the owner a new occurrence, which would retire
  attached views at the first iteration.

Free-standing views of owned memory are the form that broke `unfold`, a
freeing call and an `ensuring` interface when it was tried for every
function on 2026-10-08 (12 tests). Loop proofs in the corpus do not hit
those, which is evidence about the corpus and not about the rule.

Regression: a function with a loop that reads through an owned resource in
the body, then unfolds it after the loop; the same with a freeing call.

Done when: one mode serves both, either by re-attaching the views to the
owner's occurrence at a loop head or by authorizing the read where it
happens without leaving a view.

## C. Tactics

### C1. Short proof forms where they are not yet used

Proofs that pass were rewritten on 2026-10-08: a `have` or `ensures` proved
by a one-step block uses the brace-less form (`by T(args);`, `by simp;`), and
`have P by simp;` is `have P;`. No `by { simp(); }` remains in examples or
the standard library. Left in the long spelling:

- Every expected-failure mdtest, because a failing short `have` reports less
  than the block form
  (`bugs/a-failing-short-have-reports-less-than-the-block-form.md`). Respell
  them when that is fixed.
- The Rust examples and the sidecars under `design/charon-trial`, which are
  hash-pinned in `design/charon-trial/parity.json`.
- A few mdtests a Rust test searches by text (`bubble_sort3_loop_sorted.md`,
  `cpp_guard_unwind_before_second.md`,
  `post_execution_have_checks_each_path.md`).

## Decided and closed, for the record

- `unfold(pred)` keeps both of its meanings; it is documented as a
  branch-wide transparency switch.
- `owns p` for a pointer is the pointer's own slot. `owns *p` is what it
  points at.
- A separate tactic for conjunction and disjunction goals was dropped;
  `assumption()` closes them.
- `requires`, `ensures`, `fact` and `invariant` stay four words: each says
  where its proposition holds.
- `requires` takes no label. Requirement labels were removed on 2026-09-23
  when proofs began citing a precondition by its proposition, and nothing
  would read one. `invariant` takes a label, which names it in a failure.
- A range at another width gets no form. Closed 2026-10-08 after an
  inventory by text search: no Click source names a second width for a
  range. Reading at another width happens in C (`(unsigned char*)(void*) q`,
  `memcpy` on a wider object, about 48 files) and the kernel's byte view
  handles it (`docs/internals/byte-representation.md`). A specification that
  must state one byte of a wider cell writes the explicit load,
  `load_uint8(byte_offset(p, n))`.
- `diverges` stays on the signature and `decreases` stays a clause: one is a
  property of the function, the other a measure with an expression.

## Related defects

- `bugs/a-symbolic-struct-count-range-is-not-usable.md`
- `bugs/memory-diagnostics-print-cells-for-ranges-that-are-not-one-place.md`
