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

### A4. Rust sidecars in Rust syntax: respelling and the refusals

Decided 2026-10-08: a Rust sidecar looks like Rust, and Click's own words
(`requires`, `owns`, `result`, the tactics) are the same in every language.
Design and order of work: `design/rust-sidecar-signatures.md`.

Built: `fn` signatures with Rust type names, `as` casts, `&T` and `&mut T`
(`*value`, `parent.left`), slices as one name (`bytes.len()`, `*bytes`, a
`usize` parameter as an index), references to arrays, and `impl` blocks with
`self`. `click expand`, `profile` and `audit` address them. Reference:
`docs/reference/rust.md`, "Signatures in Rust syntax". All sixteen Rust
examples take their signatures from the Rust source, with their mirrored
copies under `design/charon-trial`.

Remaining:

- Refuse `->` and the C-shaped signature for a Rust source, with the
  spelling to write. Waits on `design/charon-trial/adler2`, which another
  work stream changes daily: its sidecars are the last C-shaped ones, and a
  new or touched one uses Rust syntax (decided 2026-10-11; the note is in
  its README). Every other Rust sidecar is converted, the tests' inline
  ones included, except `a_rust_sidecar_states_its_signature_in_rust_syntax`
  in `src/surface/tests/surface_syntax.rs`, which compares the two
  spellings and becomes the refusal's test. The five frozen originals are
  hash-pinned and stay.
- Claim labels, diagnostics and `click expand` print the importer's names
  and C-shaped places for a Rust sidecar (`__rust_q_I4_quad_I4_walk.contract`,
  `bytes_len`, `views bytes[0u64..bytes_len]`). They parse back; they are
  not what the sidecar writes.

Lifetimes and tuple fields (`self.0`) are accepted. An array or slice by
value, a reference to a reference, a non-scalar slice element and a generic
function are refused in the sidecar because the importer refuses them.

Done when: every Rust example and trial sidecar is in Rust syntax, the
C-shaped form is refused for a Rust source, and no diagnostic for one
prints a C-shaped place.

## B. Contracts and resource declarations

Found in the third pass and ruled on 2026-10-07. Nothing is open; the
rulings are under "Decided and closed".

## C. Tactics

Nothing is open. C1, the short proof forms (`by T(args);`, `by simp;`,
`have P;`), is used everywhere except the five hash-pinned originals under
`design/charon-trial`, `into-slices/sum.click` (a byte-for-byte copy of one
of them), and the Adler sidecars, which take it as they are touched.

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
  would read one. A resource's `fact` takes none either: a refused fold
  names the fact by its declaration. `ensures` and `invariant` take a
  label, which names the claim in a failure.
- A range at another width gets no form. Closed 2026-10-08 after an
  inventory by text search: no Click source names a second width for a
  range. Reading at another width happens in C (`(unsigned char*)(void*) q`,
  `memcpy` on a wider object, about 48 files) and the kernel's byte view
  handles it (`docs/internals/byte-representation.md`). A specification that
  must state one byte of a wider cell writes the explicit load,
  `load_uint8(byte_offset(p, n))`.
- Holding a resource, viewed or owned, lets C read the memory it owns
  directly; a write needs `unfold`, and a child's memory is not read
  through. The views are attached to the owner and retire with it. The
  kernel derives them again wherever it makes the owner anew: at a loop
  head, from the definition or under the invariants, and at a fold of a
  resource with fields, as views of the cells the fold consumed.
- A C++ reference local reads in a proof as a reference parameter does:
  `r` is the referent and `&r` its address. A struct reference local waits
  on the importer admitting one.
- A resource without fields holds a child that has them by a hidden
  record, which remembers the child's values across a fold. A rule under
  which each unfold yields fresh values was considered and dropped: the
  kernel treats a fieldless resource's body as a function of its arguments
  and memory in about thirty places.
- A call binds a callee's instance binder automatically when only one
  binding is possible, and never chooses between two.
- `diverges` stays on the signature and `decreases` stays a clause: one is a
  property of the function, the other a measure with an expression.

## Related defects

- `bugs/a-symbolic-struct-count-range-is-not-usable.md`
- `bugs/memory-diagnostics-print-cells-for-ranges-that-are-not-one-place.md`
