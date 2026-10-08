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

### A1. C++ reference parameters (in progress)

Today a C++ `int& value` is declared in the sidecar as `int32* value` and
read as `value[0]`. Decided: a reference is a property of the parameter. The
sidecar writes `int32& value`, `const int64& nValue`, `struct cell& c`; the
name is the referent (`owns value`, `value == old(value) + 1`, `c.value`,
`owns c`); the signature check refuses `int32*` for an `int&`.

The representation is settled: a reference parameter is an object, and what
the function receives is that object's address. The pointer that carries
`int& value` is therefore named `&value`, in the lowered C++ function, in the
checked interface and in the sidecar's parsed signature
(`reference_carrier_name` in `src/languages/c/syntax.rs`). The sidecar's
`value` parses to a read through that pointer and `&value` to the pointer.
Printers already treat `&x` as the address of a named object, so the referent
prints as `value`, a field as `c.field`, and the address as `&value`, with no
parameter list in hand, and printed text parses back to what it came from.
A dedicated syntax-tree node was tried first and dropped: it fixed printing
of contract expressions only, not of kernel terms or of a callee's contract
instantiated at a call.

The implementation is a stash in the task worktree (`git stash list` in
`/home/lacker/click-execute-single`, "wip: C++ reference parameters, carrier
named &value"). On 2026-10-07 it failed 28 of 5,872 tests, all C++ import
tests, in these groups:

- About 14 negative tests in `tests/cpp_import.rs` that make a false
  contract by replacing a substring such as `value[0]` in a passing sidecar.
  The replacement no longer matches, so the test verifies the true contract.
  Respell each, and assert the replacement changed the text.
- Three sidecars still written with a pointer for a struct reference
  (`field_first`, `predicate`, `Store`), and one that writes `*` on a
  reference (`arithmetic.click`).
- Postconditions that compare a pointer with a reference, which must now
  take its address: `ensures state.pointer == &value`.
- `old(nValue)` inside a `theorem ... executes` proof: "unknown old-state
  variable `nValue`". The old-state lookup needs the carrier's name.
- Two proofs whose printed `if` or `have` condition does not lower after
  expansion ("the kernel lowering produced 0 paths"), not yet diagnosed.
- `const_reference_preserves_qualification_and_may_alias_a_mutable_reference`:
  a read through a const reference that aliases a mutable one reports
  `missing resource fact views &readable[0]`. That is both a missing
  authority to work out and a fact that should print as `readable`.
- `examples/basic-cpp/increment.click` must match the copy quoted in the
  documentation.

Regression: the C++ fixtures under `tests/fixtures/cpp-verification` with
reference parameters, converted; a sidecar that writes `int32*` for an
`int&`, refused with both spellings named; `click expand` on a proof that
names a reference parameter, re-verified.

Done when: `scripts/check.sh` and `scripts/check.sh --audit` pass with every
C++ sidecar in the repository converted, and a C sidecar that writes `&` in a
signature is refused.

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

### B1. Child resources are written two ways

A resource without fields writes a child as `contains inner(p);`. A resource
with fields writes `owns item: inner(p);`, and that form is refused in a
resource without fields ("a named child resource requires a field-bearing
parent resource"). In examples and the standard library there are 18 of the
first and 53 of the second.

Decided: one spelling. `owns name: inner(p);` is accepted in any resource and
`contains` is retired, refused with the spelling to write.

Regression: a resource without fields that holds a named child, used by a
contract and unfolded in a proof; `contains inner(p);` refused.

Done when: no `contains` child clause remains in the repository and
`scripts/check.sh` and `scripts/check.sh --audit` pass.

### B2. Labels only on `ensures`

`ensures same: result == p->value;` is accepted. `requires nonnull: p != 0;`
is a syntax error ("expected comparison operator in `proposition`, got
`:`").

Decided: `requires` and `invariant` take a label as `ensures` does.

Regression: a labelled `requires` and a labelled `invariant`, each cited by
its label where an `ensures` label can be cited today.

Done when: those pass and the reference documents one label rule for all
three.

### B3. Reading through a declared resource

Recorded in the third pass: `views outer(p)` let C read the resource's
memory without an `unfold`, while `owns outer(p)` did not. On 2026-10-07 a
nested case did not confirm it: with `contains inner(p)` in `outer`, both
`views outer(p)` and `owns outer(p)` needed the `unfold`. Re-check with a
resource whose body owns memory directly before deciding anything.

### B4. A contract can be accepted and unusable

Recorded in the third pass: a contract that both owns and produces the same
place, `owns p->value; produces p->value;`, was accepted, and no caller
could use it. On 2026-10-07 the same contract is refused where the function
itself is checked, with "claim Ensure(2) on path 0 has mismatched proposition
completion evidence; the checked path outcome is a runtime error", which
does not say what is wrong.

Decided: refuse the contract where it is declared, with a message that names
the place held twice.

Regression: the contract above, refused at its declaration by that message,
with and without a proof block.

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

### C2. `intro() as name` on a range quantifier

`intro() as name` chooses the name of the variable a proof introduces. It is
refused on a range quantifier: for a goal `(lo..hi).all(|k| { ... })`,
`intro() as i;` fails with "`intro() as i` requires a goal written as
`forall (x: T) { ... }`". Bare `intro()` works on the same goal. It is also
untested on a `forall` over an algebraic type.

```click
theorem range_goal(n: int32) {
    ensures (0..n).all(|k| { k == k }) by {
        intro() as i;
        intro();
        normalize();
    }
}
```

A range quantifier keeps its binder in the lambda, so
`universal_goal_renamed_for_intro` in
`src/surface/proof/proof_object/step_application.rs` has no binder to
respell. Rename the lambda parameter and its uses the way the `forall` case
renames its binder, with the same rule that the new name is not in scope.

Regression: an mdtest with the theorem above expecting `pass`, a theorem
whose later step reads the variable under its new name, and a case for a
`forall` over a `spec enum` type.

Done when: those pass, a name already in scope is refused with the existing
message, the `intro() as name` row in `docs/reference/tactics/index.md` no
longer lists the range quantifier as refused, and `click expand` on a tactic
after such an `intro() as` re-verifies.

## Decided and closed, for the record

- `unfold(pred)` keeps both of its meanings; it is documented as a
  branch-wide transparency switch.
- `owns p` for a pointer is the pointer's own slot. `owns *p` is what it
  points at.
- A separate tactic for conjunction and disjunction goals was dropped;
  `assumption()` closes them.
- `requires`, `ensures`, `fact` and `invariant` stay four words: each says
  where its proposition holds.
- `diverges` stays on the signature and `decreases` stays a clause: one is a
  property of the function, the other a measure with an expression.

## Related defects

- `bugs/a-symbolic-struct-count-range-is-not-usable.md`
- `bugs/memory-diagnostics-print-cells-for-ranges-that-are-not-one-place.md`
