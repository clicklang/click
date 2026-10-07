# The tactics after a proof `if` belong to the one arm that is still live

The `else` arm of the proof `if` steps the C `if` and its `return`, so it
reaches function exit. The `then` arm only records its case and stops at the
C `if`. One arm is live, so the tactics after the proof `if` are that arm's
and run once, in it. Nothing is repeated, and no `ensuring` is needed: there
is no second arm to rejoin.

The live arm here is the first one written. The proof returns to it after
the second arm has finished.

```c filename=proof_if_one_arm_returns_and_the_other_continues.c
int32 pick(int32 x) {
    if (x == 0) {
        return 1;
    }
    return 0;
}
```

```click
verifying "proof_if_one_arm_returns_and_the_other_continues.c";

int32 pick(int32 x) {
    ensures result == 0 or result == 1;
} by {
    if x != 0 {
        have x != 0 by { assumption(); }
    } else {
        step();
        step();
        simp();
    }
    step();
    step();
    step();
    simp();
}
```

```expect
pass
```
