# `arithmetic()` before the function exit names itself in the decline

`arithmetic()` closes a focused proposition goal. Between execution steps
there is no such goal, only the execution, so the refusal names the tactic and
where the frontier stands, and says to step to the function exit first. A
`have ... by { ... }` also has a goal for it.

```c filename=c_grouped_arithmetic_mid_execution.c
int32 bump(int32 n) { return n + 1; }
```

```click
verifying "c_grouped_arithmetic_mid_execution.c";

int32 bump(int32 n) {
    requires 0 <= n;
    requires n <= 100;
    ensures result <= 101;
} by {
    arithmetic() using { 0 <= n; n <= 100; };
    execute();
    simp();
}
```

```expect
fail: `arithmetic` works on the outcome claims at function exit and does not execute
```
