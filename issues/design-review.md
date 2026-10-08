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

### B3. Reading through a declared resource (decide)

Checked on 2026-10-08 with `resource flat(p: struct cell*) { owns p->value;
owns p->other; }` and a function that reads `p->value`:

- `views flat(p);` verifies with no `unfold`. C reads the memory the
  resource owns directly.
- `owns flat(p);` does not. It needs `unfold(flat(p));` before the read and
  `fold(flat(p));` after.
- Neither reads through a child. With `resource outer(p) { owns inner(p);
  owns p->other; }`, a read of memory `inner` owns fails under `views
  outer(p);`, with and without `unfold(outer(p));`.

So a view reads one level through a declared resource and ownership reads
none. Decide whether the two should agree, and at what depth.

### B4. Overlapping places returned by one contract

A contract that returns the same place twice, `owns p->value; produces
p->value;` or `produces X; produces X;`, is refused where it is declared,
with a message naming the place.

Two places that overlap without being the same clause are not:
`owns *p; produces p->value;`, or `owns q[0..n]; produces q[1];`. With a
proof, the function is refused when its exit state is checked, with "two
owned memory resource clauses overlap", which does not name them. A
`contract` declaration with no proof is accepted.

The declaration check is by spelling because an `owns` clause is read at
entry and a `produces` clause at exit. Deciding overlap for different
spellings needs the two places compared in one state, and a place reached
through a loaded pointer can differ between the two.

Regression: `owns *p; produces p->value;` refused at its declaration by a
message naming both places, in a function with a proof and in a `contract`
with none.

## C. Tactics

### C1. Use the short proof forms in the existing proofs

The examples, standard library and mdtests are what a reader learns Click
from. Three short forms landed after most were written, and the corpus still
spells the long ones:

- `by T(args);` for a one-step proof, where the corpus writes
  `by { T(args); }` (#332). `by simp;` already existed for `by { simp(); }`.
- `have P;`, which is `have P by simp;` (#313).
- `instantiate(F, value);` without a `using` list, which looks each
  instantiated guard up as an exact fact (#307).

Counted on 2026-10-07 in mdtests, examples, stdlib and integrations: 700
`by { simp(); }`, 147 `by { assumption(); }`, 70 `by { normalize(); }`, and
about 200 `instantiate` calls with a `using` list. How many of those lists
are exactly the guards has not been counted; trying the bare form on each
and keeping the ones that still verify gives the number.

A mechanical rewrite with no change to what any proof proves. Leave a
multi-step block, a block form such as `both { ... } and { ... }`, and any
`instantiate` whose list derives a guard from other facts. Do not touch the
hash-pinned sidecars under `design/charon-trial` without updating
`parity.json`, and do not change an mdtest whose point is the long spelling
(`empty_using_list_is_accepted.md`,
`by_takes_one_tactic_without_braces.md`).

Regression: none new; the rewritten proofs are the regression.

Done when: `scripts/check.sh` and `scripts/check.sh --audit` pass, no
`by { simp(); }` remains in examples or stdlib, and the pull request reports
how many `instantiate` calls were rewritten and how many were left.

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
