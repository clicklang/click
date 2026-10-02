# An unsigned count-down loop owes an unsigned descent

`while (x > 0u) x--;` over a `uint32 x` declares `decreases x`, a `uint32`
measure. Its bundle owes the constant-true nonnegativity member, since every
unsigned value is a natural number, and the decrease member
`x - 1 <u x` at the entry value of `x`, which the guard `x >u 0` makes true.

An unsigned order is the signed order of sign-flipped operands, so the
closer does not relate `x - 1` to `x` by signed arithmetic. It closes the
member with `uint32_positive_predecessor_strictly_decreases`, after reading
the guard the other way round.

```c filename=an_unsigned_count_down_loop_owes_an_unsigned_descent.c
int32 drain(uint32 x) {
    while (x > 0u) {
        x--;
    }
    return 0;
}
```

```click
verifying "an_unsigned_count_down_loop_owes_an_unsigned_descent.c";

int32 drain(uint32 x) {
    ensures result == 0;
} by {
    loop {
        decreases x;
        initialize by { simp(); }
        preserve by {
            step();
            close_invariants();
        }
    }
    execute();
    simp();
}
```

```expect
pass
```
