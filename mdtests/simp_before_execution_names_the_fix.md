# `by simp;` on a function postcondition names the fix

`simp` reasons about the state at function exit and never runs the C body,
so a postcondition proved `by simp;` is refused before any statement runs.
The refusal says what to write instead: `execute();` first, or `by auto;`,
which executes and then simplifies.

```c filename=simp_before_execution.c
int32 clamp_low(int32 x) {
    if (x < 0) return 0;
    return x;
}
```

```click
verifying "simp_before_execution.c";

int32 clamp_low(int32 x) {
    ensures result >= 0 by simp;
}
```

```expect
fail: `simp` requires execution to reach function exit first; write `execute();` before it, or prove the claim `by auto;`
```
