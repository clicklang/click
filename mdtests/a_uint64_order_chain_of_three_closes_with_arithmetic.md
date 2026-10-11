# A `uint64` order chain of three closes with `arithmetic`

`arithmetic() using` proves a 64-bit order goal from a chain of three listed
order premises, `i < n`, `n <= m` and `m <= length`, as it does from two: the
Integer step adds the third premise whole to a pair. The same holds over
`int32`.

`a_uint64_order_chain_with_a_gap_is_refused.md` breaks the chain.

```click
theorem chain_of_three(i: uint64, n: uint64, m: uint64, length: uint64) {
    requires i < n;
    requires n <= m;
    requires m <= length;
    ensures i < length by { arithmetic() using { i < n; n <= m; m <= length; } }
}
theorem int32_chain_of_three(a: int32, b: int32, c: int32, d: int32) {
    requires a < b;
    requires b <= c;
    requires c <= d;
    ensures a < d by { arithmetic() using { a < b; b <= c; c <= d; } }
}
```

```expect
pass
```
