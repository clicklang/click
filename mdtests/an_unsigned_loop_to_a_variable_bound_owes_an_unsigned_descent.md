# An unsigned loop to a variable bound owes an unsigned descent

`while (x < n) x++;` over `uint32` values declares `decreases n - x`, a
`uint32` measure computed with C's wrapping subtraction. Its decrease member
is `(n - x) - 1 <u n - x` at the entry value of `x`. That holds exactly when
`n - x` is not zero, which the guard `x <u n` gives, so no invariant is
needed: the measure is ranked on the wrapped value C computes, and the
guard is what keeps that value from wrapping.

The claim is true, but closing it needs unsigned order arithmetic over the
sign-bit-flipped differences, which the closer does not do yet. That open
decrease member is the refusal this test pins; it changes to `pass` when
`bugs/unsigned-order-arithmetic-in-closers.md` is fixed.

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
fail: `((n - at(statement(3).entry, x)) - 1) < (n - at(statement(3).entry, x)) (unsigned)` remained open; this loop declares `decreases`, so the bundle also has `0 <= n - x` at the back edge, `n - x` decreases at the back edge
```
