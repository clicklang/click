# An unsigned order chain composes like a signed one

`x < n` and `n <= 4u32` over `uint32` give `x < 4u32`, as the same chain
over `int32` gives `x < 4`. Both premises are `uint32` orders, so `solve()` and
`solve() using` sum them over the operands' `uint32` observations, as
they sum a `uint64` chain, and no definedness side condition is owed.

```click
theorem below_by_solve(x: uint32, n: uint32) {
    requires x < n;
    requires n <= 4u32;
    ensures x < 4u32 by {
        solve();
    }
}

theorem below_by_arithmetic(x: uint32, n: uint32) {
    requires x < n;
    requires n <= 4u32;
    ensures x < 4u32 by {
        solve() using {
            x < n;
            n <= 4u32;
        };
    }
}

theorem at_most_by_arithmetic(x: uint32, n: uint32) {
    requires x <= n;
    requires n <= 4u32;
    ensures x <= 4u32 by {
        solve() using {
            x <= n;
            n <= 4u32;
        };
    }
}
```

```expect
pass
```
