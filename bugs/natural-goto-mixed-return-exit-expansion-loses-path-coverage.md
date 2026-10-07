# A natural cycle with return and forward goto exits cannot expand

## Violated invariant

A verified proof with retained checked paths should expand to a simple
certificate covering every accepted path. A natural cycle with one terminal
return and one continuing forward goto verifies and retains checked execution
traces, but whole-claim expansion sees two frame paths and one surface path.

## Reproduction

`mdtests/natural_goto_forward_exit_and_return.md` is a complete passing
reproduction: count down nonnegative `n`; return 7 when `n == 1`, jump to
`done` when `n == 0`, and return `n` there. The contract is
`result == 0 or result == 7`; the proof uses `loop`, `execute()`, and `simp()`.

Observed on 2026-10-07 after preserving the loop's checked forward jump:
ordinary verification passes and both accepted paths have checked steps.
`expand_c0_claim_source` refuses with
`surface/certificate path coverage diverged at p1: surface has 1 paths but frame certificate has 2`.
The focused regression is
`natural_goto_mixed_return_retains_paths_and_reports_expansion_gap` in
`src/surface/tests/loop_tests.rs`.

## Intended regression and acceptance

Make the fixture expand and reverify through the ordinary checker. Retain
both the terminal return and the continuing jump, with each path's facts and
postcondition obligations. Change the diagnostic regression to assert an
accepted expansion and cold recheck. Do not drop a path or change the C into
another control-flow shape.

Inspect `append_surface_tactics_by_leaf` in
`src/surface/proof/execution_state.rs` and the retained loop-return paths in
`src/surface/proof/cursor_execution.rs` and
`src/surface/proof/proof_object/outcomes_and_focus.rs`.
