# A proof-level `if` whose arms only reason rejoins

The `if` splits the proof on the sign of `x` between two C statements. Each
arm proves the same fact from its own case, and neither runs C nor changes
the state, so the two cases rejoin: the statements after the `if` are checked
once, from one state, with the fact both arms established. The case facts
themselves do not survive the join.

```c filename=proof_if_arms_rejoin.c
int32 bump(int32 x) {
    int32 a;
    a = 0;
    a = a + 1;
    return a;
}
```

```click
verifying "proof_if_arms_rejoin.c";

int32 bump(int32 x) {
    ensures result == 1;
    ensures x <= 0 or x > 0;
} by {
    step();
    step();
    if x <= 0 {
        have x <= 0 or x > 0;
    } else {
        have x <= 0 or x > 0;
    }
    step();
    step();
    simp();
}
```

```expect
pass
```
