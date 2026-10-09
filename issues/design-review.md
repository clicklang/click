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

The "C operation" line of a failure prints a read through a reference as
the sidecar writes it, `value` or `c.first`: a step records the stepped
function's reference parameters, and the printer of a kernel term consults
them (`describe_read_through_reference` in `src/surface/diagnostics.rs`).
`click expand` does the same from the sidecar's function block
(`ParameterPlaceScope`): a read through a scalar reference is `value`, and
a read at a scalar field of a struct is the field place, `c.second` through
`struct cell& c` and `p->second` through a struct pointer, parameter or
local.

One gap remains: a field of a struct nested in another (`p->inner.x`) is
still expanded in kernel spelling, `load_int32(byte_offset(p, 4))`, because
the printer matches scalar fields of the outer struct only. It parses back
and verifies.

Regression: `click expand` on a branch over `p->inner.x` writes the
condition with the field place.

Done when: no expansion prints `load_...` for a field of a struct.

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

- Five examples keep `bytes_len` and `(int32)` casts in their contracts and
  proofs: `rust-loops`, `rust-iterators`, `rust-iter-references`,
  `rust-byte-sum` and `rust-chunks-exact`. A test compares each one's
  contract, as parsed, with its frozen original under `design/charon-trial`
  (`charon_migrated_sidecars_preserve_original_source_contracts`), and the
  respelled form parses to a different tree. Respell them once that test
  compares meaning, not syntax. A cast on an index that is not a lone
  parameter stays everywhere until typed indices cover it (A5).
- Then refuse `->` and the C-shaped signature for a Rust source, with the
  spelling to write.
- Diagnostics and `click expand` print C-shaped spellings for a Rust
  sidecar (`bytes[0..(int32)bytes_len]`). They parse back; they are not what
  the sidecar writes.
- A 32-bit index is the memory model's limit, so a slice contract states
  `requires bytes.len() <= 2147483647u64`. Dropping it needs range bounds
  wider than 32 bits in the kernel (A5).
- An array by value, a reference to a reference, generics and lifetimes in
  a `fn` signature are refused.

Done when: every Rust example and trial sidecar is in Rust syntax, the
C-shaped form is refused for a Rust source, and no diagnostic for one
prints a C-shaped place.

### A5. An index keeps its type until it is an offset

Design, kernel survey and order of work: `design/typed-indices.md`.

Stage 1 is built: a 64-bit range bound of any form, and a 64-bit parameter
written alone as an index, need no cast. The contract still states
`requires n <= 2147483647`, and one that does not is refused at setup with
the requirement to state.

Remaining:

- **Stage 3, order reasoning over 64-bit terms.** It is the next thing to
  do, ahead of stage 2: a C function that reads `bytes[index + 1]` with a
  `size_t` index cannot be verified today whatever its contract says. The
  body's read is refused with "missing resource fact
  `views bytes[(truncate32(index) + 1)]`" under `requires index + 1 <
  length`. Regression: that function verifying.
- **Stage 2, the extent is `isize::MAX`.** Removes `requires n <=
  2147483647`. It cannot be done piece by piece and needs scaling
  regressions. Check with Lacker before starting it.
- A 64-bit index expression that is not a lone parameter still takes the
  cast in a contract. It follows stage 3.

Done when: no contract casts an index, and a slice contract states no bound
on its length.

## B. Contracts and resource declarations

Found in the third pass and ruled on 2026-10-07. Nothing is open; the
rulings are under "Decided and closed".

## C. Tactics

### C1. Short proof forms where they are not yet used

Proofs that pass were rewritten on 2026-10-08: a `have` or `ensures` proved
by a one-step block uses the brace-less form (`by T(args);`, `by simp;`), and
`have P by simp;` is `have P;`. No `by { simp(); }` remains in examples or
the standard library. Left in the long spelling:

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
