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

A first implementation exists as a stash in the task worktree
(`git stash list` in `/home/lacker/click-execute-single`, "wip: C++ reference
parameters"). It is not green. It may be rebuilt from the design section
"Reference parameters" instead; what it established is recorded there. The
three things still to build:

- The referent gets its own syntax-tree node that prints as the bare name.
  Built as the node `value[0]` produces, it prints as `value[0]`, and
  `click expand` parses that again as the referent indexed once more.
- `&value` on a reference parameter is its address, for postconditions that
  compare pointers (`state->pointer == &value`, and a struct reference
  compared with a receiver).
- Negative tests in `tests/cpp_import.rs` that make a false contract by
  replacing a substring such as `value[0]` must be respelled, each with an
  assertion that the replacement changed the text.

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

## B. Contracts and resource declarations (decide)

Found in the third pass and not yet ruled on. Each was checked against the
tool on 2026-10-07 unless it says otherwise.

### B1. Three words for a proposition

A proposition is introduced by `requires` or `ensures` in a contract, `fact`
in a resource body, and `invariant` in a loop header. Decide whether these
stay three words or share one.

### B2. Child resources are written two ways

A resource without fields writes a child as `contains inner(p);`. A resource
with fields writes `owns item: inner(p);`, and that form is refused in a
resource without fields ("a named child resource requires a field-bearing
parent resource"). In examples and the standard library there are 18 of the
first and 53 of the second. Decide whether one spelling serves both.

### B3. Labels only on `ensures`

`ensures same: result == p->value;` is accepted. `requires nonnull: p != 0;`
is a syntax error ("expected comparison operator in `proposition`, got
`:`"). Decide whether every proposition clause takes a label.

### B4. `diverges` and `decreases`

Termination is stated in two positions: `diverges` on the signature and
`decreases` as a clause in the body. Decide whether both belong in one
place.

### B5. Reading through a declared resource

Recorded in the third pass: `views outer(p)` let C read the resource's
memory without an `unfold`, while `owns outer(p)` did not. On 2026-10-07 a
nested case did not confirm it: with `contains inner(p)` in `outer`, both
`views outer(p)` and `owns outer(p)` needed the `unfold`. Re-check with a
resource whose body owns memory directly before deciding anything.

### B6. A contract can be accepted and unusable

Recorded in the third pass: a contract that both owns and produces the same
place, `owns p->value; produces p->value;`, was accepted, and no caller
could use it. On 2026-10-07 the same contract is refused where the function
itself is checked, with "claim Ensure(2) on path 0 has mismatched proposition
completion evidence; the checked path outcome is a runtime error", which
does not say what is wrong. Decide whether such a contract is refused when
it is declared, with a message that names the place held twice.

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

## Related defects

- `bugs/a-symbolic-struct-count-range-is-not-usable.md`
- `bugs/memory-diagnostics-print-cells-for-ranges-that-are-not-one-place.md`
