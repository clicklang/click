# A 64-bit countdown closes its back edge

After `i -= 1` under the guard `i > 0`, the back edge owes `0 <= i` and
`i <= n` of the decremented counter. `close_invariants()` closes each member
with `simp()`, and reads a member it cannot close as spelled once more at the
iteration entry, `at(<entry>, 0 <= i - 1)`, so the step sees the difference
the body took; over the back-edge locals it reads `0 <= i`, which the guard
at the iteration entry does not mention. Its `Integer` certificate cites the
guard `i > 0` for its reading `0 < to_integer(i)`. The `uint64` exit `not (i > 0)`
leaves `i == 0`, since no `uint64` is below zero.

```c filename=countdown.c
int64_t countdown(int64_t n) {
    int64_t i = n;
    while (i > 0) {
        i -= 1;
    }
    return i;
}

uint64_t countdown_unsigned(uint64_t n) {
    uint64_t i = n;
    while (i > 0) {
        i -= 1;
    }
    return i;
}
```

```click
verifying "countdown.c";

int64 countdown(int64 n) {
    requires n >= 0;
    ensures result == 0;
} by {
    step_until(loop(0));
    loop {
        decreases i;
        invariant 0 <= i and i <= n;
    }
}

uint64 countdown_unsigned(uint64 n) {
    ensures result == 0;
} by {
    step_until(loop(0));
    loop {
        decreases i;
        invariant i <= n;
    }
}
```

```expect
pass
```
