# Differing natural goto exit states leave joined facts without Click spellings

## Violated invariant

A checked loop-exit join should retain usable facts about its successor.
When forward edges assign different constants to the same local before jumping
to one label, the kernel joins the states but the proof search cannot retain a
complete certificate for the true disjunction of returned values.

## Reproduction

`mdtests/natural_goto_forward_exit_differing_states.md` contains the complete
supported C and Click reproduction: count down from nonnegative `n`, set `n`
to 7 on the `n == 0` exit or to 9 on the `n == 1` exit, then return `n` at the
shared label. The proof uses `loop`, `execute()`, and `simp()` with the true
postcondition `result == 7 or result == 9`.

Observed on 2026-10-07 after retaining forward jumps in the loop rule:
`checked outcome simp search did not retain a complete proof`, with
`some premises have no exact Click spelling at this frontier`. Both edges
reach the label and the failure is prompt. The same-state sibling
`natural_goto_forward_exit_multiple_edges_state.md` verifies.

## Intended regression and acceptance

Change the differing-state fixture from its current diagnostic expectation to
`pass`. Preserve each edge's state and facts, retain an accepted checked proof
trace, and expand and reverify the proof through the ordinary verifier. Do not
drop an exit or weaken the contract to make it pass.

Investigate `join_loop_exits` and `LoopExitRestatement::restate` in
`src/kernel/loops.rs`, and the surface spelling of joined facts at loop-exit
snapshots in `src/surface/proof/cursor_execution.rs`.
