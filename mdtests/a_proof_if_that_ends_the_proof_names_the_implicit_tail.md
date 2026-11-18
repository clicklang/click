# A proof `if` that ends the proof names the implicit tail when it cannot rejoin

Nothing is written after this proof `if`, but the implicit tail that ends
every proof still follows it and is checked once. The `then` arm takes no
step and the `else` arm takes one, so the two live arms end at different
program points and cannot rejoin. The refusal says that the implicit tail is
what follows, rather than claiming that tactics were written after the `if`,
and says how to finish each arm.

```c filename=a_proof_if_that_ends_the_proof_names_the_implicit_tail.c
void dec(int32* p) {
    if (*p == 1) {
        *p = 0;
    } else {
        *p = *p - 1;
    }
}
```

```click
verifying "a_proof_if_that_ends_the_proof_names_the_implicit_tail.c";

void dec(int32* p) {
    owns p[0..1];
    requires 1 <= p[0];
    ensures p[0] == old(p[0]) - 1;
} by {
    if p[0] == 1 {
    } else {
        step();
    }
}
```

```expect
fail: the arms of this proof `if` do not rejoin: nothing is written after the `if`, but the implicit tail that ends the proof follows it and is checked once, so each arm must reach the function exit or end where the other does, in the same state. End each arm with `step_until(function.exit);`
```
