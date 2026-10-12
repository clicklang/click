# Naming every value and program point

Design for the spelling gap in [smt-auto](../issues/smt-auto.md) milestone 4.
Each value the checker introduces gets a source name when it is created, so
any fact can be printed as Click source where the proof stands. Names cite
program points with the selectors Click already has; W1 of
[design-review](../issues/design-review.md) is answered without new syntax.
Code references are to master at `72bf15c0`.

## The problem

Smart tactics turn what they find into ordinary steps, and every step is
written in source. `auto` can only rewrite by an equality it can write down,
`simp` can only cite a premise it can write down, and `click expand` prints
both. A fact is written down today by looking it up in a map from facts to
the text that introduced them (`SurfacePropositionMap`). A fact with no entry
has no spelling.

On `examples/rbtree-erase/rbtree_erase_color_flips_red_all.click`, eight
`by auto` probes looked up 511 connected equalities. 236 had no spelling. The
existing synthesizer (`surface_synthesis.rs`), which rebuilds source from the
current C state, named none of the 236. The misses are:

- equalities over trees and contexts the proof built with `let`, `fold` and
  match bindings, such as `is_rb(..) == 1` and `ctx_rb(..) == 1`;
- C field values read before a later write, such as the
  `__rb_parent_color` word of a node already rewritten;
- equalities between symbolic pointers.

The synthesizer cannot name these because it never reads proof bindings, and
it names memory only in the current state, at `old(...)`, and in one extra
snapshot that only loop bundles supply. Nothing searches the snapshots that
`step()` records.

## Goals

- Every value the checker introduces has a name that is valid source where
  the proof stands, or a recorded reason it has none.
- A fact over named values prints as source, and the print is checked by
  lowering it again.
- Work stays linear: one record per introduced value, made when it is
  introduced, and printing proportional to the printed fact
  (`docs/internals/verification-efficiency.md`).
- No C changes, and no new program-point syntax.

## Non-goals

- Naming a particular loop iteration's visit. A snapshot key keeps its latest
  visit today, and that does not change.
- Making `simp` or `auto` find more proofs. This only removes spelling
  failures.

## Program-point names

No new syntax. A generated name cites a program point the proof already
records:

- a `mark` or loop name the proof wrote at that point, when there is one;
- otherwise `statement(N).entry` or `statement(N).exit`, which `step()`
  records for every statement it executes.

Statement text anchors (`at(entry "tmp = sibling->rb_left;", tmp)`) were
considered and rejected. They survive C edits that renumber statements, but
the C under proof is fixed and rarely edited, and when it is, the nearby
proof usually needs work anyway. In exchange they need parser and lowering
support, a tiebreaker for repeated text (about a fifth of the statements in
the examples share their exact text with another in the same function, by a
rough count), rules for long statements and macros, and a migration tool.
Line numbers were rejected too: they break in the same way as statement
numbers, and also on any comment or blank line above.

For W1, the existing answer stands: a point the proof refers to more than
once is named with `mark` or `loop as name`, which live in the proof and
survive C edits, and `statement(N)` is for one-off and generated references
(`docs/concepts/proof-workflow.md` already recommends this).

To use an existing mark, `mark` records which statement boundary it sits on,
one map entry per mark. A generated name looks the point up there before
falling back to `statement(N)`.

## Value names

Each value gets a name recorded when it is created: a persistent map from
kernel variable (or symbolic pointer block) to a Click expression and the
scope in which it is valid. The map lives with the proof state it describes,
in `ProofLocals` for proof bindings and in the execution presentation for C
values, so branches share it and a join keeps the entries valid on all arms.

| Introduced by | Allocated at | Name |
|---|---|---|
| Function parameter | `surface/lowering/resource_lowering.rs:127` | `p`, or `at(function.entry, p)` once `p` is reassigned (synthesis already does this) |
| C memory read | `kernel/eval/memory_loads.rs:3627` | `at(statement(N).entry, e)`, where `N` is the reading statement and `e` the expression it reads, or a mark at that point. The load registry is keyed by snapshot and pointer, so the statement is known at minting |
| Loop havoc | `kernel/loops.rs:9377` | `at(loop.entry, x)` for the havocked local `x` |
| Call result or resource from a call | `kernel/functions.rs:5560` | `at(statement(N).exit, x)` for the destination `x`, or the `let r = step()` name |
| Branch join | `kernel/api.rs:1736` | `at(statement(N).exit, x)` for the joined local `x` of the `if` statement `N` |
| `malloc`, `realloc` | `kernel/eval/statements.rs:1118` | `at(statement(N).exit, p)` for the destination pointer |
| `choose`, `obtain` | `surface/proof/proof_object/fixed_state_steps.rs:752`, `:858` | The bound name, already in `ProofLocals` |
| Proof `match` arm | `surface/proof/proof_object/match_cases.rs:251` | The arm's binder name, valid inside the arm |
| `intro` | `kernel/proof/object.rs:1041` | The binder name in `surface_bindings`, valid in that goal |
| `fold`, `unfold` binding | parser, `surface/parser.rs:~6170` | The bound name, `n.model` for a field |

Most rows invert a name→value map Click already keeps. The C-read, havoc,
join and `malloc` rows are new records. Values with no row (composite
witnesses, mutex and publication bookkeeping, kernel ADT case witnesses) stay
unnamed, and a fact over them has no spelling, as today.

A name is used only where it is valid: a binding in scope, and a program
point recorded on this path. Validity is not tracked separately. Every print
is lowered again and kept only if it denotes the same fact, which is already
the rule for recorded spellings outside a C outcome.

## Printing a fact

The printer walks the kernel fact once and replaces each value by its name
from the map, using the existing surface constructors for operators,
functions and constructors. Lookup is logarithmic and output is linear in the
fact, so there is no search. The result is lowered and compared to the fact.
On a mismatch or an unnamed value, the fact has no spelling, and the caller
reports which value was unnamed and where it came from.

Uses, in order:

1. `auto`'s rewrite search and integer refutation (`solver_bridges.rs`).
2. `simp` premise citation (`resolve_simp_premises`).
3. Diagnostics: "recent premises" print raw kernel terms today, such as
   `int32 =(black(Walk::At(d, rest:Walk)), 1) is true`.

The recorded fact-to-text map stays as the first lookup, since it keeps the
text the author wrote.

## Scaling

One map insertion per introduced value, at the point it is introduced, adds
logarithmic work to a step that already allocates the value. Printing is
proportional to the fact printed. Nothing scans snapshots, facts or bindings.
A multi-size regression (a straight-line chain of reads and a loop with
growing havoc sets) checks that per-step work does not grow with earlier
values.

## Milestones

1. **Proof bindings.** The value-name map, filled from `choose`, `obtain`,
   match arms, `intro`, `fold` and `let = step()`, plus the printer, used by
   `auto` and `simp`. Measured on the rbtree file with the probe described
   above.
2. **C values.** Names for C reads, loop havoc, joins, calls and `malloc`,
   citing a mark at the point when there is one and `statement(N)`
   otherwise. Measured again; most of the 236 misses are expected to be C
   reads and proof bindings, but that is a guess until then.
3. **Diagnostics.** Premises and goals printed through value names.
