# Launch design review: open critiques

Priority: P1.

Soundness: soundness-adjacent. This file is a tracker. Items M1 (no
independent checker) and M2 (no written semantics) are trust questions
without a known false acceptance. Each item that becomes a reproduced false acceptance is filed in
`bugs/` with its own label.

Items P1–P4, W4 and W5 waited on the SMT-backed `auto`
([design/smt-auto-stage1.md](../design/smt-auto-stage1.md)), which landed;
P3 and P4 are done, P2 (Integer-default specification arithmetic) moved
to [standard-library.md](standard-library.md), and the others are ruled
below. Also depends on [simplify-step.md](simplify-step.md), which now holds the
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
excluded): six of 53 examples are over the 20-lines-per-line-of-C target in
`docs/internals/verification-efficiency.md`.

- `rbtree-augmented`: 40x by lines, 93x by tokens.
- `rbtree-erase`: 36x by lines, 119x by tokens.
- `rbtree-insert`: 35x by lines, 71x by tokens.
- Both Rust iterator sums: 33x by lines.
- `arena`: 21x by lines.

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

## W. Proof workflow and tooling

### W4. Expansion output is hard to read

Done: `click expand` writes each repeated derivation of an arithmetic
certificate once and leaves out derivations its conclusion does not use. A
grouped closure whose claims `normalize();` proves is written as one
`normalize();` before the remaining closers when that form verifies
(`examples/vector-push/vector_push.click`). Committed expansions were tidied
the same way where they still verify.

Today: certificate nodes are still numbered, and sibling certificates under
one `both` repeat the same premise and interval nodes, which one certificate
cannot share with another (`mdtests/bubble_sort3_two_pass_sorted.md`).
Closures that `normalize();` cannot shorten keep one `assumption();` per
obligation, and older committed expansions keep restatements such as
`have 0 == 0 by normalize();`.

Proposed fix: named, deduplicated certificate nodes, and expansions that
drop the noise.

Decision: split (maintainer, 2026-10-15). Committing expansions is intended:
expansion is how a slow smart site is made fast, so the certificate cache
the review proposed instead is ruled out (see W5 in
[design/proof-language-rulings.md](../design/proof-language-rulings.md)).
That makes readable expansion output matter more; it stays open.

### W6. Some diagnostic lines still print kernel notation

Facts, goals, rejected requirements, evaluated sides, search candidates and
the proof context now print in Click or C syntax (`old(g[0]) < 100`,
`(uint32)n <= 1073741823u32`, `viewable(p[1..2])`), with reads of other
memories as `at(<state A>, ...)` defined after the report. `--trace-proof`
keeps its typed notation by design.

Today: a loop-carried value inside the body prints as the iteration's entry
value, `at(statement(N).entry, i)`, and a refused C operation names an address
a local holds through that local (`alias->mu`, `*shared`, `p[i].y`). An
`ensures` refusal names the returned value `result`, a value or allocation a
local held at a recorded statement boundary as that local there
(`at(statement(1).exit, r)`, `at(statement(2).exit, buf)`), and a read of a
recorded snapshot's memory through that snapshot's locals. A pure theorem's
`Integer` binder prints as its name in a conversion-condition refusal, and a
memory-history sentence names a struct-typed global's field (`g.b`) where
exactly one scalar field occupies exactly the bytes accessed. What remains:

- A callee's result that no local ever held, as in `return value() + 1;`,
  prints as `<unnamed A>`. Its only spelling is a translation temporary: the
  C call `value()` is not a Click expression, and re-evaluating it would be
  another call.
- An address no local held exactly at a recorded snapshot, such as an
  element `buf + u` of an allocation, prints as `<pointer A>`; so do the
  `recent premises` lines, which are rendered without the execution's
  snapshot names.
- A store at a constant offset into a struct-typed local prints as `s+8`:
  the function's table of local struct types is keyed by source spelling,
  while a local's block carries its kernel name, so a shadowing declaration
  of another type could hold the block that spelling would find. Union
  members sharing an offset and width keep the offset by design
  (`mdtests/global_union_members_sharing_bytes_keep_the_offset.md`).

Proposed fix: carry each struct-typed local's layout with its kernel block
name; spell an address inside an allocation as an offset from the local that
held its base; give the `recent premises` lines the report's snapshot names.

Decision: in progress.

## L. Surface language

### L4. Rust and C++ specs still read like C

Today: Rust sidecars write Rust types, `*const u8`, `as` and `bool` in pure
functions, predicates and theorems, a parenthesized comparison is a `bool`
value, and a C or C++ `bool` parameter is a claim. What remains: a pure
function cannot take a slice (`bytes: &[u8]` with its own `.len()`), so it
takes `*const u8` and a `usize` length; Rust literal spellings without a
Click equivalent (`4usize`, `4i32`, `1_000`) are refused; the shared lemma
library is named by C types (`uint64_less_than_to_integer`); and the
archived Charon-trial sidecars under `design/charon-trial` keep the C
spellings they were written in.

Proposed fix: slice parameters for pure functions, passed as the slice; the
remaining literal suffixes; Rust-spelled aliases or names for the lemmas a
Rust proof applies.

Decision: fix (maintainer, 2026-10-13), after L2: Rust types, `as` and `bool` throughout Rust sidecars. Types, `as` and `bool` done; the items above remain.

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
