# A chain bound closes in its non-strict form

`x < n` and `n <= 4` give `x < 4`, which is `x <= 3` written the other way.
A chain that ends at `4` concludes the strict form, so `simp` proves that
and restates it; `arithmetic() using` adds the two premises directly.

```click
theorem signed_by_simp(x: int32, n: int32) {
    requires x < n;
    requires n <= 4;
    ensures x <= 3 by { simp(); }
}

theorem unsigned_by_simp(x: uint32, n: uint32) {
    requires x < n;
    requires n <= 4u32;
    ensures x <= 3u32 by { simp(); }
}

theorem signed_by_arithmetic(x: int32, n: int32) {
    requires x < n;
    requires n <= 4;
    ensures x <= 3 by { arithmetic() using { x < n; n <= 4; } }
}

theorem unsigned_by_arithmetic(x: uint32, n: uint32) {
    requires x < n;
    requires n <= 4u32;
    ensures x <= 3u32 by { arithmetic() using { x < n; n <= 4u32; } }
}
```

```expect
pass
```
