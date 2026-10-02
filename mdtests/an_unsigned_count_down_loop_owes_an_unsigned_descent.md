# An unsigned count-down loop owes an unsigned descent

`while (x > 0u) x--;` over a `uint32 x` declares `decreases x`, a `uint32`
measure. Its bundle owes the constant-true nonnegativity member, since every
unsigned value is a natural number, and the decrease member
`x - 1 <u x` at the entry value of `x`, which the guard `x >u 0` makes true.

The claim is true, but closing it needs unsigned order arithmetic: the
closer reads `x - 1 <u x` as a signed order between the sign-bit-flipped
values `(x - 1) ^ 2^31` and `x ^ 2^31`, and does not relate the two. That
open decrease member is the refusal this test pins; it changes to `pass`
when
`bugs/unsigned-order-arithmetic-in-closers.md` is fixed.

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
fail: `x < at(statement(1).entry, x) (unsigned)` remained open; this loop declares `decreases`, so the bundle also has `0 <= x` at the back edge, `x` decreases at the back edge
```
