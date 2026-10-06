# A proof-level `if` whose arms run the same C statement rejoins

Each arm of the `if` steps `a = 0;` under its own case and then proves the
same fact. Both arms end before `a = a + 1;` in the same state, so the two
cases rejoin there: the rest of the function is checked once, from one state,
with the fact both arms established.

```c filename=proof_if_arms_rejoin_after_c_steps.c
int32 bump(int32 x) {
    int32 a;
    a = 0;
    a = a + 1;
    return a;
}
```

```click
verifying "proof_if_arms_rejoin_after_c_steps.c";

int32 bump(int32 x) {
    ensures result == 1;
} by {
    step();
    if x <= 0 {
        step();
        have x <= 0 or x > 0 by { simp(); }
    } else {
        step();
        have x <= 0 or x > 0 by { simp(); }
    }
    step();
    step();
    simp();
}
```

```expect
pass
```
