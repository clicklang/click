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

### A3. Reference locals in C++ bodies

A local `int& r = x;` is named in a proof through the lowered program, where
it is a pointer. After A1 it should read as its referent there too. Not
started; needs a look at how proofs name C++ locals before it is scoped.

### A4. Rust sidecars in Rust syntax: the pinned examples and the refusals

Decided 2026-10-08: a Rust sidecar looks like Rust, and Click's own words
(`requires`, `owns`, `result`, the tactics) are the same in every language.
Design and order of work: `design/rust-sidecar-signatures.md`.

Built: `fn` signatures with Rust type names, `as` casts, `&T` and `&mut T`
(`*value`, `parent.left`), slices as one name (`bytes.len()`, `*bytes`, a
`usize` parameter as an index), references to arrays, and `impl` blocks with
`self`. `click expand`, `profile` and `audit` address them. Reference:
`docs/reference/rust.md`, "Signatures in Rust syntax". Eight of the sixteen
Rust examples are converted.

Remaining:

- Eight examples keep the C-shaped form: `rust-arrays`, `rust-loops`,
  `rust-iterators`, `rust-iter-references`, `rust-byte-sum`,
  `rust-chunks-exact` and `rust-split-at` are compared byte for byte with
  pinned copies under `design/charon-trial` (`tests/rust_import/parity.rs`,
  `array_lengths.rs`, `iterator_proof.rs`, `loop_headers.rs`,
  `src/languages/rust/charon/split_slices_tests.rs`), and three tests split
  the text of `rust-move-drop` by its function headers. Convert each
  example with its pinned copy and regenerate
  `design/charon-trial/parity.json`.
- The converted examples take their signatures from the Rust source, but
  their contracts and proofs still write `bytes_len`, `->` and
  `(int32)index`. Respell them.
- Then refuse `->` and the C-shaped signature for a Rust source, with the
  spelling to write.
- Diagnostics and `click expand` print C-shaped spellings for a Rust
  sidecar (`bytes[0..(int32)bytes_len]`). They parse back; they are not what
  the sidecar writes.
- A 32-bit index is the memory model's limit, so a slice contract states
  `requires bytes.len() <= 2147483647u64`. Dropping it needs range bounds
  wider than 32 bits in the kernel.
- An array by value, a reference to a reference, generics and lifetimes in
  a `fn` signature are refused.

Done when: every Rust example and trial sidecar is in Rust syntax, the
C-shaped form is refused for a Rust source, and no diagnostic for one
prints a C-shaped place.

## B. Contracts and resource declarations

Found in the third pass and ruled on 2026-10-07. Each was checked against the
tool that day unless it says otherwise.

### B1. A second fact about a child's field, where the parent has fields

Built: a resource that declares no `field` may name a child that has
fields and state facts about them. It keeps the child's fields in a record
the author does not write, is held without a name (`owns pair(p);`), and is
unfolded and folded with only the child map. A call binds a callee's
instance binder without a map when only one binding is possible. Reference:
`docs/reference/language/index.md`.

One asymmetry remains. In a parent that declares fields of its own, the
one equation `fact first.v == total;` ties a child's field to a parent
field, and any other fact that mentions `first.v` is refused as "duplicate
child field equation". A parent without fields has no such limit, because
`first.v` there reads the hidden field.

Regression: a parent with a declared field, the equation for the child's
field, and a second fact `fact p->n == first.v;`, accepted and usable after
an unfold.

Done when: a fact may mention a named child's field in any resource, with
one of them, or a hidden field, still fixing where the value is kept.

### B3. Reads through an owned resource with fields, across a loop

Decided 2026-10-08 and built: holding a resource, viewed or owned, lets C
read the memory it owns directly. A write still needs `unfold`. Depth stays
at one level: memory a child resource owns is not read through.

For a resource without fields this is one mechanism. The views of its memory
are attached to the owner's occurrence, so they retire when the owner is
unfolded, consumed, freed or handed to an interface, and a loop head derives
them again for each owner the loop declares, from the definition over the
head's memory (`with_owner_read_authority_rederived` in
`src/kernel/loops.rs`). They are never kept across a loop: at exit the kernel
restores the frame from before the loop, and a view of an address the
definition read out of memory then would be stale.
`mdtests/a_freed_cell_is_not_read_through_another_owner_after_a_loop.md` is
the use after free that keeping them accepted.

A resource with fields follows the rule in a proof without a loop: a plain
body, or the arm the requirements select, gives views attached to the owner
(`mdtests/c_reads_through_an_owned_resource_with_fields.md`).

What remains is a resource with fields in a proof that contains a loop
(`OwnedCores::InstanceArmsStanding` in `src/surface/proof/resources.rs`).
A selected arm's views are free-standing there, as before the decision, and
a plain body gives no read authority at all, because the facts that say
which memory the resource owns hold at the loop's exit, and nothing derives
attached views again at that point. Attaching them
without that step fails 13 mdtests, among them `loop_owns_modeled_instance`,
`rb_next` and `rb_prev`, with a read after the loop refused.

Free-standing views of owned memory are not retired with their owner, which
is what blocks a later `free` of that memory. Whether one can go stale as
the fieldless case did has not been examined.

Regression: `loop_owns_modeled_instance.md` verifying with attached views;
a resource with fields whose arm owns a cell at an address read from its
model, saved before a loop that changes the model, not readable through the
saved pointer afterwards.

Done when: read authority for a resource with fields is derived at a loop's
exit under the exit's facts, `InstanceArmsStanding` is gone, and a `free`
after a loop of memory one owner held is accepted while another owner stays
folded (today refused: "resource would remain usable after its allocation
is freed").

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
