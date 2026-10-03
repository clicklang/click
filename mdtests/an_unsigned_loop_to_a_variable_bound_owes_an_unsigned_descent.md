# An unsigned loop to a variable bound owes an unsigned descent

`while (x < n) x++;` over `uint32` values declares `decreases n - x`, a
`uint32` measure computed with C's wrapping subtraction. Its decrease member
is `(n - x) - 1 <u n - x` at the entry value of `x`. That holds exactly when
`n - x` is not zero, which the guard `x <u n` gives, so no invariant is
needed: the measure is ranked on the wrapped value C computes, and the
guard is what keeps that value from wrapping.

The closer states the two steps with the `uint32` order lemmas: the
difference is nonzero under the guard, and the predecessor of a nonzero
`uint32` is smaller.

```c filename=an_unsigned_loop_to_a_variable_bound_owes_an_unsigned_descent.c
int32 count(uint32 n) {
    uint32 x = 0u;
    while (x < n) {
        x++;
    }
    return 0;
}
```

```click
verifying "an_unsigned_loop_to_a_variable_bound_owes_an_unsigned_descent.c";

int32 count(uint32 n) {
    ensures result == 0;
} by {
    step();
    step();
    loop {
        decreases n - x;
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
