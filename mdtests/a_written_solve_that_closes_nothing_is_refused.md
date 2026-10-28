# A written `solve() using` that closes nothing is refused

At function exit, reached with `step_until(function.exit)`, a written
`solve() using` acts on the first open goal. Here
it cites a premise that does not hold, so it closes nothing and is refused
with that goal. It used to be skipped, leaving the implicit closer to close
the claim and `click expand` to drop the written tactic.

```c filename=a_written_solve_that_closes_nothing_is_refused.c
int32 zero(void) {
    return 0;
}
```

```click
verifying "a_written_solve_that_closes_nothing_is_refused.c";

int32 zero() {
    ensures result == 0 by {
        step_until(function.exit);
        solve() using { 1 == 2; }
    }
}
```

```expect
fail: `ensures result == 0` failed for `zero.ensures_0` path 0: unclosed goal
```
