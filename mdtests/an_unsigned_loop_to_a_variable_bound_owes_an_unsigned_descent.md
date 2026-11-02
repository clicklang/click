# An unsigned loop to a variable bound owes an Integer descent

`while (x < n) x++;` over `uint32` values declares `decreases n - x`,
an exact Integer difference. The guard proves that the increment cannot
wrap and that the next measure is nonnegative. The closer emits the
operation identity for the increment and proves strict Integer descent.
No extra invariant is needed.

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
        initialize by { solve(); }
        preserve by {
            step();
        }
    }
}
```

```expect
pass
```
