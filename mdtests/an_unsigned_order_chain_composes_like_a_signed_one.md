# An unsigned order chain composes like a signed one

`x < n` and `n <= 4u32` over `uint32` give `x < 4u32`, as the same chain
over `int32` gives `x < 4`. Both are signed orders between sign-bit-flipped
atoms (`(x ^ 2^31) < (n ^ 2^31)` and `(n ^ 2^31) <= (4 ^ 2^31)`), so
`simp` and `arithmetic() using` sum them the way they sum signed bounds,
and the certificate spells the sum as the chain's end comparison
`x < 4u32`. A flipped atom is an opaque value: the sign-bit flip is total,
so no definedness side condition is owed.

```click
theorem below_by_simp(x: uint32, n: uint32) {
    requires x < n;
    requires n <= 4u32;
    ensures x < 4u32 by {
        simp();
    }
}

theorem below_by_arithmetic(x: uint32, n: uint32) {
    requires x < n;
    requires n <= 4u32;
    ensures x < 4u32 by {
        arithmetic() using {
            x < n;
            n <= 4u32;
        }
    }
}

theorem at_most_by_arithmetic(x: uint32, n: uint32) {
    requires x <= n;
    requires n <= 4u32;
    ensures x <= 4u32 by {
        arithmetic() using {
            x <= n;
            n <= 4u32;
        }
    }
}
```

```expect
pass
```
