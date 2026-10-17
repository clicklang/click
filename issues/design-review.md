# Launch design review: open critiques

Priority: P1.

Soundness: soundness-adjacent. This file is a tracker. Items M1 (no
independent checker) and M2 (no written semantics) are trust questions
without a known false acceptance. Each item that becomes a reproduced false acceptance is filed in
`bugs/` with its own label.

Items P1–P4, W4 and W5 waited on the SMT-backed `auto`
([design/smt-auto-stage1.md](../design/smt-auto-stage1.md)), which landed;
P3 and P4 are done, W4, W5 and W6 are closed in
[design/proof-language-rulings.md](../design/proof-language-rulings.md), P2
(Integer-default specification arithmetic) moved to
[standard-library.md](standard-library.md), and P1 is below. Also depends on [simplify-step.md](simplify-step.md), which now holds the
critique that "simple" `step()` is not simple (formerly W3).

On 2026-10-12 Click was reviewed the way an expert launch audience would
review it, from four sides: the surface language, the proof and tactic
workflow, the memory and resource model with its trust story, and a
newcomer's first hour. This file lists every critique that review raised.
Each one gets an explicit ruling, **fix** or **wontfix**, with the reason; a
critique is not dropped by being forgotten. Delete an item when its fix,
regression and documentation land, or when it is ruled wontfix and the
ruling and its reason are moved to `design/proof-language-rulings.md` (or
another design document where the ruling belongs). Delete this file when it
is empty.

Every item starts as **Decision: open**. Record the maintainer's ruling in
place before work starts.

Documentation has two audiences. The repository and `docs/`, the AI
reference, are written for AI readers: an agent asked to evaluate or use Click
reads them, so they must be precise, complete and honest about limits.
Human-facing material (the top of the README, the guide in `guide/` and a
public website) is written by the maintainer, so critiques of human onboarding,
such as jargon load and positioning against other verifiers, are the
maintainer's and are not tracked here.

## Violated invariant

A reader of Click's launch material can verify a small function in their own
C code in an hour, understand what was proved and what was trusted, and
write proofs whose size and fragility are in proportion to the code. Each
item below is a place where that is not yet true, or where a launch reviewer
is likely to say it is not.

## Why Dafny and Verus proofs are so much shorter

Context for items P1–P4. Dafny and Verus generate one verification
condition per method and hand it to an SMT solver (Z3), which does linear
arithmetic, congruence closure, case splitting and quantifier instantiation
without being asked; the user writes specs, loop invariants and occasional
hints. Their specs use mathematical integers; Dafny is designed for
verification and Verus inherits aliasing and memory safety from Rust's type
system. Click deliberately trusts no external solver: every step is checked
by its own kernel, smart tactics expand into simple checkable steps, search
is bounded and deterministic, and it verifies arbitrary existing C, so memory
safety, undefined behavior and aliasing are its own obligations. That buys
reproducible verdicts and inspectable proofs, and costs length. Published
SMT-based systems work reports proof-to-code ratios in the low single digits;
seL4 in Isabelle is roughly 20x, about Click's own target
(`docs/internals/verification-efficiency.md`). The way to close most of the
gap without giving up checkability is the Lean `omega`/`linarith` model:
decision procedures that search freely and emit certificates the kernel
checks.

## P. Proof size and automation

### P1. Proofs are far larger than the code

Today (2026-10-16, `scripts/proof-ratio.py`, comments and blank lines
excluded): three of 53 examples are over the 20-lines-per-line-of-C target in
`docs/internals/verification-efficiency.md`.

- `rbtree-augmented`: 40x by lines, 93x by tokens.
- `rbtree-erase`: 36x by lines, 119x by tokens.
- `rbtree-insert`: 35x by lines, 71x by tokens.

`arena` was 21x and is 19.6x after its hand-written `have` proofs that
`auto` closes within 10% of each claim's work were shortened; the edits
inside one `have` of `arena_pipeline` are held back by
`bugs/whole-file-verify-multiplies-a-control-tactics-work.md`. Both Rust
iterator sums were 33x and are 18.1x: `have` proofs `auto` closes are
`by auto()`, and `have` steps the proof does not need are gone, each within
10% of the claim's original work.

Token ratios run two to four times the line ratios because proof lines are
long: `rbtree_erase_color_flips_red_all.click` is 518 KB with lines over
1,300 characters.

Proposed fix: Integer-default specification arithmetic
([standard-library.md](standard-library.md)) and the landed P6 (loop facts carry across steps
and the back edge closes implicitly), plus a published proof-to-code budget
per example that the gate reports.

Done when: the examples meet a stated budget, or the budget and the reason
for exceeding it are published.

Decision: fix (maintainer, 2026-10-15). The gate reports each example's
proof-to-code ratio against the 20x budget, report-only at first; Integer-default
specification arithmetic is the main remaining lever for meeting it.

Progress: the report is in. `scripts/check.sh` ends by listing the examples
over the target, with token ratios beside line ratios. What remains is
bringing those examples under the target, or publishing the reason each one
exceeds it.

### P5. Copy-paste across case files and sidecars

Today: `rb_erase` and `__rb_erase_augmented` each have one general contract
(R2, below). The general erase-color repair proof's left and right arms
(about 1,380 lines each) are mirror images, and so are the general unlink's
left and right exits. C++ caller sidecars repeat callee contracts
(`examples/basic-cpp/with_restore_caller.click`).

Proposed fix: [design/proof-reuse.md](../design/proof-reuse.md):

- R2: one general contract per function, including one general `rb_erase`
  contract with a theorem that its cases are exhaustive.
- R3: automatic unfolding of recursive spec functions.
- R4: automatic opening and closing of resources.
- R5: one script for several arms.

Decision: fix (maintainer, 2026-10-14), starting with R2.

R2 is done (2026-10-14): general `__rb_erase_augmented` and `rb_erase`
contracts replace 16 per-case sidecars of `examples/rbtree-erase`; see
[design/proof-reuse.md](../design/proof-reuse.md#r2-one-general-contract-per-function).
R3 is in: `simp` evaluates recursive specification functions over known
constructors to a fixed fuel (see the status under R3 in
[design/proof-reuse.md](../design/proof-reuse.md#r3-automatic-unfolding-of-recursive-specification-functions)).
Rewriting the erase-color arms with it waits on the object-class regression
that keeps `rbtree-erase` from verifying. R4 and R5 remain.

## L. Surface language

### L4. Rust and C++ specs still read like C

Today: Rust sidecars write Rust types, `*const u8`, `as` and `bool` in pure
functions, predicates and theorems, a parenthesized comparison is a `bool`
value, a C or C++ `bool` parameter is a claim, and Rust literal spellings
(`4usize`, `4i32`, `1_000`) are accepted, and a pure function takes a slice
(`bytes: &[u8]` with its own `.len()`). What remains: the shared lemma
library is named by C types (`uint64_less_than_to_integer`); and the
archived Charon-trial sidecars under `design/charon-trial` keep the C
spellings they were written in.

Proposed fix: Rust-spelled aliases or names for the lemmas a Rust proof
applies, after P2's Integer-default specification arithmetic settles which
lemmas remain.

Decision: fix (maintainer, 2026-10-13), after L2: Rust types, `as` and `bool` throughout Rust sidecars. Types, `as`, `bool`, literal suffixes and pure-function slices done; the items above remain.

## M. Memory model, semantics and trust

### M1. There is no independent proof checker

The trusted base is now listed in `docs/concepts/trust.md`: kernel (about
254,000 lines of Rust), obligation construction, the C front end and target
model, importers, prelude theorems applied without re-checking, and `extern`
contracts. Replacing the README's kernel-design essay is the maintainer's
human-facing work.

Today: `click expand` and `click audit` re-check proofs with the same kernel
and lowering, so a bug there is invisible to them; there is no serialized proof
object and no independent checker.

Proposed fix: serialize proof objects and write a small independent checker
that re-checks them.

Decision: fix, after performance and completeness (maintainer,
2026-10-14). Proving the kernel sound as a whole is not a current priority:
it would slow the priorities, which are performance at the scale of large
real-world projects and then completeness, both measured in practice. A
false acceptance, once found, is still fixed first, as a bug.

### M2. No written semantics or soundness argument

Today: the resource algebra and loan ledger are described in prose
(`docs/internals/separation-logic.md` calls its notation "explanatory";
`docs/internals/stable-views.md` lists laws without proof).

Proposed fix: a paper-level operational semantics and a model of views and
loans, with fold/unfold and loan recovery argued sound against it.

Decision: fix, after performance and completeness (maintainer,
2026-10-14). Proving the kernel sound as a whole is not a current priority:
it would slow the priorities, which are performance at the scale of large
real-world projects and then completeness, both measured in practice. A
false acceptance, once found, is still fixed first, as a bug.

## Strengths the review credited

Recorded so fixes do not trade them away: verification of unchanged source
with pinned hashes; deterministic verdicts from work budgets; smart search
never trusted, expansion and audit re-checked; documentation tied to passing
fixtures; precise statements of what is proved (termination, undefined
behavior, `diverges`); readable resource verbs with the write footprint equal
to ownership; allocation lifetime separate from access; candid scoping such
as Adler-32's "remains unproved".
