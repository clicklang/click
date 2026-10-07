# A natural `goto` cycle's `return` exit is dropped, so the contract is vacuous

## Violated invariant

A loop rule's exits must cover every way the C leaves the loop. A function
written as a label, a body that `return`s on one branch, and a backward
`goto` (`natural_control_loop`, lowered by
`src/surface/lowering/annotations.rs:1041` to `while (1) { body }` with a
`backedge_target`) leaves through that `return`. Its contract must be checked
on the returned value.

The surface registers the returning preservation path as a
`CLoopFinalExitCandidate` (`is_natural_return_exit` in
`src/surface/proof/execution_planning/loop_planning.rs`, about line 1290).
The kernel's `execute_c_while_exit_paths` (`src/kernel/loops.rs`, the
`for candidate in final_exit_candidates` block after
`prepare_loop_top_state`) treats every candidate as a state at which the
guard is re-read and keeps it only on the guard-false branch:
`assume_condition_truthiness(candidate.state(), condition, ..., false, ..)`.
The natural loop's guard is the literal `1`, which is never false, so every
candidate yields no exit, `join_loop_exit_paths` returns `None`, and the
rule's only path is `VerificationDiverges`. The function's `ensures` is then
discharged vacuously. (The surface's `is_return_exit` arm for ordinary
`while` loops drops the path outright; see
`return-inside-summarized-loop-body-is-dropped.md`.)

## Reproduction

`maybe_stop(0)` returns `7`; `ensures result == 0` verifies, and
`--trace-proof` reports no checked path at all.

```markdown
```c filename=g.c
int32 maybe_stop(int32 flag) {
again:
    if (flag == 0) {
        return 7;
    }
    flag = 0;
    goto again;
}
```

```click
verifying "g.c";

int32 maybe_stop(int32 flag) {
    requires flag >= 0;
    ensures result == 0;
} by {
    loop {
        invariant flag >= 0;
        decreases flag;
    }
    simp();
}
```
```

Observed:

```text
$ click verify repro.md
1 selected proof verified
$ echo $?
0
$ click verify --trace-proof maybe_stop repro.md
proof trace (checked tactics and branch facts):
  <no checked simple steps recorded on this path>
1 selected proof verified
```

`mdtests/natural_goto_cycle.md` is this program with `return 0` and
`ensures result == 0`; it passes for the same vacuous reason.

## Intended regression

The repro above as a negative mdtest (expect `fail`), plus a sibling that
returns `flag + 1` on the exit branch under `ensures result == 1`, which must
pass only because the return path is actually certified. A third case: a
function whose every path ends in `return` inside a natural cycle under
`ensures false` must fail.

## Acceptance criteria

- A natural cycle's `return` exit reaches contract certification as a
  `Return` outcome with its value and state; it is never evaluated as a
  guard-false exit of the synthetic `while (1)`.
- A loop rule whose only path is `VerificationDiverges` is formed only when
  the loop has no reachable exit, not when the exits were candidates the
  guard could not falsify.
- The negative regressions fail and name the `return`; the positive one passes.
