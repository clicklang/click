# Launch design review: open critiques

Priority: P1.

Soundness: soundness-adjacent. This file is a tracker. Items M1 (no
independent checker), M2 (no written semantics) and M3 (`memcpy` reading under
`viewable`) are trust questions without a known false acceptance. Each item that becomes a reproduced false acceptance is filed in
`bugs/` with its own label.

Items P1–P4, W4 and W5 waited on the SMT-backed `auto`
([design/smt-auto-stage1.md](../design/smt-auto-stage1.md)), which landed;
P3 and P4 are done and the others are ruled below. Also depends on [simplify-step.md](simplify-step.md), which now holds the
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

Today: `examples/rbtree-erase` is 39,047 lines of `.click` for 322 lines of
C (about 120x, six times the 20x target in
`docs/internals/verification-efficiency.md`);
`rbtree_erase_color_flips_red_all.click` alone is 518 KB with lines over
1,300 characters. `examples/rust-byte-sum` proves a 9-line loop in about 184
lines; `examples/modeled-binary-tree` proves the 12-line `tree_contains` in
about 100. `examples/arena/arena_cells.click` is 5,537 lines for 279 lines
of C.

Proposed fix: items P2 and P6, plus a published proof-to-code budget per
example that the gate reports.

Done when: the examples meet a stated budget, or the budget and the reason
for exceeding it are published.

Decision: fix (maintainer, 2026-10-15). The gate reports each example's
proof-to-code ratio against the 20x budget, report-only at first; P2 and P6
are the main levers for meeting it.

### P2. Spec arithmetic is machine arithmetic

Today: `+` in a specification is the C operation and is partial
(`docs/reference/language/index.md`, "an int32 fold's `+` is partial in
specifications"). Proofs bridge with `to_integer`, width-specific lemmas
(`int64_less_equal_transitive` and about 110 more in `library/`)
and hand-written `arithmetic_certificate` blocks: about 270 lines of
`examples/bounded-pool/bounded_pool.click` show counters do not overflow.
ACSL, Dafny and Verus specs use mathematical integers by default.

Proposed fix: specification arithmetic is over `Integer` by default; C
semantics are written explicitly where a spec means them.

Done when: decided, and if fixed, the examples shrink accordingly.

Decision: fix (maintainer, 2026-10-15). Specification arithmetic is over
`Integer` by default, with these rules:

- In a specification, `+`, `-`, `*`, unary minus and the comparisons on
  machine integers are Integer operations. A machine operand widens
  implicitly, since that loses nothing; narrowing stays explicit
  (`to_int32(z)` with its bound obligations).
- Unsigned wraparound is written explicitly, with a wrapping operation or
  `% 2^N`. The migration rewrites each unsigned specification operation into
  that form, and a proof that no wrap occurs removes it.
- Integer `/` and `%` truncate toward zero, as C and ACSL do.
- Bitwise operators and shifts stay machine-typed; their results widen when
  combined with Integer arithmetic.
- `defined(e)` remains the way a specification states C evaluation.
- One switch-over by scripted migration, not a per-file mode. A prototype
  on `examples/bounded-pool` and one unsigned-heavy example comes first, to
  measure the proof that disappears and check timing against the
  [verification efficiency contract](../docs/internals/verification-efficiency.md).

Progress: a prototype on `examples/bounded-pool` written in Integer form
shrinks the sidecar from 437 to 284 lines, and showed that built-in checks
read only machine facts. Step 1 is done: an Integer comparison of exact
machine observations also files its native comparison, so resource
quantities and count definedness accept Integer premises. Step 2 has
started: `arithmetic "integer";` opts a file into the rule, as a migration
switch removed when the default flips, and the kernel decides Integer
comparisons of machine observations through their native comparisons.
Under the directive, `bounded-pool`'s `pool_init` verifies with its bridge
lemmas removed; the next blocker is population counts, which are still
`int32` machine sums. Next: Integer-valued population counts, then the
migration file by file and the flip.

Afterwards, delete the `machine_integer` and `integer` lemmas Integer
arithmetic makes unnecessary, complete the families that remain, and give
those modules qualified names
([standard-library.md](standard-library.md)).

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
R3, R4 and R5 remain.

### P6. Loop proofs restate facts

Today: invariants restate immutable facts and held views
(`examples/rust-byte-sum/sum.click`), iterations end with explicit
`step(); step(); step(); close_invariants();`, and identical facts are
re-`have`d after steps (the deeper-successor arms of
`examples/rbtree-erase/rbtree_erase_augmented.click`).

Proposed fix: facts about values a step cannot change carry across steps
automatically; the back edge closes implicitly.

Decision: fix (maintainer, 2026-10-14), after the SMT-backed `auto`, which has
landed.

## W. Proof workflow and tooling

### W4. Expansion output is hard to read

Today: expanded arithmetic certificates use numbered nodes and repeat
identical blocks (`mdtests/bubble_sort3_two_pass_sorted.md`); committed
expansions keep noise such as `have 0 == 0 by normalize();` and runs of
`assumption();` (`examples/vector-push/vector_push.click`).

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

### M3. Several read-permission notions and no fractions

Today: `views` (call-scoped loans), `viewable` (bounds only), reads granted
by a folded composite, and reads from match-arm selection. The trusted
`memcpy` contract reads its source under `viewable` alone
(`docs/internals/byte-representation.md`), against "external loads require a
covering viewed or owned memory resource". No fractional permissions, so no
reader-writer pattern.

Proposed fix: fractional or counted read permissions; fold `viewable` into
them; reconcile `memcpy`.

Decision: split (maintainer, 2026-10-14). Fix now: the trusted `memcpy`
contract reads its source under `views`, as every other external load does.
Fractional and counted read permissions are deferred until a program needs a
reader-writer pattern.

### M4. Field-less resources hide a record

Today: a field-less `pair(p)` keeps its child's fields "in a record the
author does not write" (`docs/reference/language/index.md`); the alternative
was dropped because the kernel treats a field-less body as a function of its
arguments in about thirty places (`design/proof-language-rulings.md`).

Proposed fix: require explicit fields, or show the record in diagnostics and
expansion. This revisits a recorded ruling.

Decision: fix (maintainer, 2026-10-14): show the record in diagnostics and
expansion output. Explicit fields are not required; the recorded ruling
stands.

## Strengths the review credited

Recorded so fixes do not trade them away: verification of unchanged source
with pinned hashes; deterministic verdicts from work budgets; smart search
never trusted, expansion and audit re-checked; documentation tied to passing
fixtures; precise statements of what is proved (termination, undefined
behavior, `diverges`); readable resource verbs with the write footprint equal
to ownership; allocation lifetime separate from access; candid scoping such
as Adler-32's "remains unproved".
