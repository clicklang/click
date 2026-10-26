# `step_until` in a `branch` arm that falls through does not name the arm limit

## Violated invariant

A refusal names its cause. A `branch` arm that does not return ends at the
C `if`'s shared continuation; the code after the `if` runs after the arms
join, not inside the arm. `step_until(function.exit)` in such an arm is
refused with "`step_until` found no checked step from this frontier", which
reads as though the C had nothing left to run. It does not say that the arm
stops at the continuation, nor where to write the steps instead. A `step()`
that runs past the end of the same arm names the limit ("`step()` ran past
the end of its branch body",
`mdtests/execute_branch_arm_stops_at_shared_continuation.md`).

## Reproduction

`sign.c`:

```c
int32 sign(int32 x) {
    if (x < 0) {
        return 1;
    }
    return 0;
}
```

```click
verifying "sign.c";

int32 sign(int32 x) {
    ensures result == 0 or result == 1;
} by {
    branch {
        step_until(function.exit);
    } else {
        step_until(function.exit);
    }
}
```

`click verify` refuses the `else` arm's `step_until` with "`step_until` found
no checked step from this frontier". The same proof with the `else` arm empty,
or with a proof `if x < 0` before the C in place of `branch`, verifies.

## Intended regression

An mdtest with the proof above, expecting a refusal that names the arm's end
at the shared continuation and says to step there after the `branch`, or to
split with a proof `if` before the C.

## Acceptance criteria

- `step_until` of any target past the end of a `branch` arm that falls
  through is refused naming that arm limit, as `step()` is.
- The refusal says what to write: the steps after the `branch`, or a proof
  `if` before the C when each path needs its own work at exit.
