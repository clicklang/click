# `by simp();` on a function postcondition names the fix

`simp` reasons about the state at function exit and never runs the C body,
so a postcondition proved `by simp();` is refused before any statement runs.
The refusal says what to write instead: `execute();` first, or `by auto();`,
which executes and then simplifies. It is the same refusal `simp` gets inside
an execution arm
([`simp_before_exit_in_arm_names_the_frontier.md`](simp_before_exit_in_arm_names_the_frontier.md)).

```c filename=simp_before_execution.c
int32 clamp_low(int32 x) {
    if (x < 0) return 0;
    return x;
}
```

```click
verifying "simp_before_execution.c";

int32 clamp_low(int32 x) {
    ensures result >= 0 by simp();
}
```

```expect
fail: Step to the exit first with `step()` (the end of the body is one step) or `execute()`, or prove the claim `by auto();`
```
