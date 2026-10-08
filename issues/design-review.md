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
`src/languages/c/syntax.rs`; design section "Reference parameters").

One printing gap remains. A contract expression prints a scalar referent as
`value`. A kernel term for the same read, as in a "C operation" line or a
condition `click expand` writes, prints `load_int32(&value)`. That parses
back correctly, but it is not what a sidecar writes. The printer cannot print
`value` there without the parameter's type: the same shape through a struct
reference, `load_int64(&box)`, is the struct's first field, not the struct.

Regression: `click expand` on a branch over a scalar reference writes the
condition with the bare name, and on a branch over a struct reference's
first field writes `box.field`.

Done when: no diagnostic or expansion prints `load_...(&name)` for a
reference parameter.

### A2. Receivers are `this`

Today a member function's receiver is a pointer parameter spelled `self`,
which the exporter delivers as a reference. Decided: it is the pointer `this`,
as in C++ (`this->fee`, `owns *this`). Do after A1.

Done when: C++ sidecars spell the receiver `this` and `self` is refused for a
C++ source with the spelling to write.

### A3. Reference locals in C++ bodies

A local `int& r = x;` is named in a proof through the lowered program, where
it is a pointer. After A1 it should read as its referent there too. Not
started; needs a look at how proofs name C++ locals before it is scoped.

### A4. Rust spellings (decide)

Decided in principle: each language spells a place its own way, so a Rust
`c: &mut Cell` is `owns *c` and `c.value`. Not designed. It is larger than a
respelling: the sidecar restates signatures in C shape
(`const uint8* bytes, uint64 bytes_len` for `bytes: &[u8]`), a slice carries
its length, tuple fields are `_0`, and layout is the compiler's. Needs its
own proposal, including whether a Rust sidecar states its signature in Rust
syntax.

### A5. A whole slice (decide)

`views bytes[0..(int32)(uint32)bytes_len]` is the only spelling for all of a
Rust slice. Whether a whole slice gets a spelling, and which, belongs with
A4.

### A6. Memory at another width (decide)

A range has the element type of its base. Some proofs read memory at another
width, for example a struct as bytes. That needs its own explicit form. Start
with an inventory of the proofs that rely on it; none has been made.

## B. Contracts and resource declarations

Found in the third pass and ruled on 2026-10-07. Each was checked against the
tool that day unless it says otherwise.

### B1. A named child in a resource without fields

A resource holds a child resource with `owns inner(p);`, the clause it uses
for memory; `contains inner(p);` is retired and refused with that spelling.

A child can also be named, `owns item: inner(p);`, so the parent's facts can
read the child's fields as `item.field`. That is accepted only in a parent
that declares fields of its own, because the parent's model is where the
child's model is kept. In a parent without fields it is refused: "this
resource declares no fields to hold them; write the child without a name".

Decide whether a parent without fields should be able to name a child. It
would need a model for a resource that declares none.

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

### B4. Overlap that depends on a symbolic bound

A contract that returns one place twice, or two places that overlap by
layout (`owns *p; produces p->value;`), is refused where it is declared or
set up, with a message naming the places.

An overlap that depends on a symbolic bound is not: `requires n >= 2;
owns q[0..n]; produces q[1];`. With a proof it is refused when the exit state
is checked, with "two owned memory resource clauses overlap", which does not
name them. A `contract` declaration with no proof is accepted.

Regression: that contract refused at setup by a message naming `q[0..n]` and
`q[1]`, in a function with a proof and in a `contract` with none.

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
- One-step blocks after `initialize`, `preserve` and `close_invariants`,
  which do not take the brace-less form: `close_invariants by simp;` is a
  syntax error. Decide whether they should.
- `instantiate(F, v) using { ... }` calls whose list is exactly the guards,
  which could drop the list. Try the bare form on each and keep the ones
  that still verify; about 200 calls have a list.
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
- `diverges` stays on the signature and `decreases` stays a clause: one is a
  property of the function, the other a measure with an expression.

## Related defects

- `bugs/a-symbolic-struct-count-range-is-not-usable.md`
- `bugs/memory-diagnostics-print-cells-for-ranges-that-are-not-one-place.md`
