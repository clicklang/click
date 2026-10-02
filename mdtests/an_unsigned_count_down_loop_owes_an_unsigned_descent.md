# An unsigned count-down loop owes an unsigned descent

`while (x > 0u) x--;` over a `uint32 x` declares `decreases x`, a `uint32`
measure. Its bundle owes the constant-true nonnegativity member, since every
unsigned value is a natural number, and the decrease member
`x - 1 <u x` at the entry value of `x`, which the guard `x >u 0` makes true.

The closer does not relate `x - 1` to `x` under the unsigned order by
itself. The proof states the two steps: the guard read the other way round,
and the predecessor of a nonzero `uint32`.

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
            have 0u32 < at(statement(1).entry, x) by {
                apply(uint32_gt_implies_reversed_lt(at(statement(1).entry, x), 0u32)) using {
                    at(statement(1).entry, x) > 0u32;
                }
            }
            have x < at(statement(1).entry, x) by {
                apply(uint32_positive_predecessor_strictly_decreases(at(statement(1).entry, x))) using {
                    0u32 < at(statement(1).entry, x);
                }
            }
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
