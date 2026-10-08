# A failing `have P;` reports less than `have P by { simp(); }`

## Violated invariant

`have P;` is `have P by simp;`, which is `have P by { simp(); }`: three
spellings of one proof step. They prove the same facts. When the step fails
they must also say the same thing, or the short spellings cost a user the
diagnosis.

## Reproduction

Take any expected-failure mdtest whose failing step is
`have P by { simp(); }` and respell that step `have P;`. Three shapes, each
reproduced on 2026-10-08:

- **A `have` during execution.**
  `mdtests/a_heap_read_back_in_the_alias_case_is_not_the_earlier_store.md`
  reports that `r == 3` "is false at this point". With `have r == 3;` it
  reports "`have` failed: `have r == 3` did not close its checked nested
  goal".
- **A `have` after execution reached the function's exit.**
  `mdtests/c_contract_executes_status_nested_rejects_inner.md` reports
  "have body tactic 1: `simp` failed for `lift.contract`: could not establish
  `cell[0] != 0`". With the short form it reports "checked outcome `have`
  search did not retain a complete proof".
- **A `have` in a pure theorem.**
  `mdtests/pure_have_reports_the_premises_it_consulted.md` reports
  "narrowing that range needs `lo <= (hi - 1)`". With the short form it
  reports "checked pure script for `last_cell.ensures_0` could not complete
  tactic 1 (`have`)".

## Cause

The parser gives the short forms `SourceProof::Tactic(SmartTactic::Simp)` and
the block form `SourceProof::Script`. Each consumer then takes a different
route for the two: the tactic form goes to a closure search that returns
"not proved" with no reason, and the script form runs the step and keeps its
error. The split is in `solve_nested_have`
(`src/surface/proof/checked_drivers/proof_execution.rs`), in the pure-theorem
`have` (`src/surface/proof/pure_theorems.rs`, near the
`SourceProof::Tactic(SmartTactic::Simp)` arms), and in the post-execution
`have` (`src/surface/proof/smart_closures.rs`).

Routing the tactic form through the script path in `solve_nested_have` alone
fixes the first shape and changes 16 existing expectations to the fuller
message; the other two shapes are untouched by it.

Because of this, the rewrite of existing proofs to the short forms
(`issues/design-review.md`, C1) left every expected-failure mdtest in its
long spelling.

## Intended regression

For each of the three shapes, one mdtest in the long spelling and a copy in
each short spelling, all with the same `expect` text.

## Acceptance

- The three spellings give the same failure text in all three shapes.
- The expected-failure mdtests can be respelled to the short forms with no
  change to their `expect` blocks.
