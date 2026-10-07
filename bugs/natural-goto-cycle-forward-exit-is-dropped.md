# A natural `goto` cycle's forward `goto` exit is dropped, so the contract is vacuous

## Violated invariant

A loop rule's exits must cover every way the C leaves the loop. A natural
cycle (a label, a body, and a backward `goto`, lowered to `while (1)` with a
`backedge_target`) can also leave through a forward `goto` to a label after
the cycle. The code at that label runs, and the function's contract must be
checked on what it returns.

The surface registers the forward-exit preservation path as a
`CLoopFinalExitCandidate` (`is_natural_exit_jump` in
`src/surface/proof/execution_planning/loop_planning.rs`), and the kernel's
`execute_c_while_exit_paths` (`src/kernel/loops.rs`, the
`for candidate in final_exit_candidates` block) keeps a candidate only on the
guard-false branch of the synthetic guard `1`, which is never false. The rule
therefore has no exit path, the loop is summarized as diverging, and the
contract is discharged vacuously. The sibling return exit was fixed by
exporting a `Return` outcome from the rule; the forward exit needs the same
treatment as a `Jump { target, state }` outcome (the step driver's `Jump` arm
already moves the frontier to the label) and
`symbolic_c_statement_execution_with_loop_rule` must accept it.

## Reproduction

`count_down(n)` returns `7`; `ensures result == 0` verifies and
`--trace-proof count_down` reports no checked step on the path.

```c filename=natural_goto_exit_label.c
int32 count_down(int32 n) {
again:
    if (n == 0)
        goto done;
    n--;
    goto again;
done:
    return 7;
}
```

```click
verifying "natural_goto_exit_label.c";

int32 count_down(int32 n) {
    requires n >= 0;
    ensures result == 0;
} by {
    loop {
        invariant n >= 0;
        decreases n;
    }
    simp();
}
```

Observed on 2026-10-07: `1 selected proof verified`, exit 0.
`mdtests/natural_goto_exit_label.md` and
`mdtests/natural_goto_multiple_exit_labels.md` are this shape with `return 0`
and pass for the same vacuous reason.

## Intended regression

The reproduction above as a negative mdtest (`fail: result == 0; left side
evaluated to 7`), a positive sibling whose exit label returns `n + 7` under
`ensures result == 7` (true only because `n == 0` at the exit), and a
two-label variant where one label returns a value the contract excludes.

## Acceptance criteria

- A natural cycle's forward `goto` exit reaches the step driver as a jump to
  its label with the state at the `goto`, and the code at the label is
  executed and certified; it is never evaluated as a guard-false exit of the
  synthetic `while (1)`.
- A loop rule whose only path is `VerificationDiverges` is formed only when
  the loop has no reachable exit.
- The negative regressions fail naming the returned value; the positives
  pass; `mdtests/natural_goto_exit_label.md` and
  `mdtests/natural_goto_multiple_exit_labels.md` keep passing for a real
  reason (their traces show a checked path).
