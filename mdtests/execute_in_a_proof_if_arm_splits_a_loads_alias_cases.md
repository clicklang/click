# `execute()` in a proof `if` arm splits a load's alias cases

After the stores `buf[u] = 7` and `buf[v] = 9`, the read `buf[0]` has one
successor per alias case. `execute()` at the top of a proof splits on the
condition that tells them apart; inside a proof `if` arm it declined, and the
proof was refused as a shape "not implemented in this execution context".
The arm's `execute()` now makes the same proof-level split, running each case
to exit. `mdtests/execute_in_a_proof_if_arm_names_the_failing_alias_case.md`
is the negative.

```c filename=execute_in_a_proof_if_arm_splits_a_loads_alias_cases.c
int32 f(int32 u, int32 v) {
    int32 r;
    int32* buf;
    buf = malloc(16);
    if (buf == 0) {
        return 0;
    }
    buf[0] = 3;
    buf[u] = 7;
    buf[v] = 9;
    r = buf[0];
    free(buf);
    return r;
}
```

```click
verifying "execute_in_a_proof_if_arm_splits_a_loads_alias_cases.c";

int32 f(int32 u, int32 v) {
    requires 0 <= u;
    requires u < 4;
    requires 0 <= v;
    requires v < 4;
    ensures u == u;
} by {
    step();
    step();
    step();
    if buf == 0 {
        execute();
        simp();
    } else {
        step();
        step();
        step();
        step();
        execute();
        simp();
    }
}
```

```expect
pass
```
