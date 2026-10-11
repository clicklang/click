# A `uint64` order chain with a gap is refused

As `a_uint64_order_chain_of_three_closes_with_arithmetic.md`, but the middle
premise runs the wrong way, `m <= n`: nothing orders `n` below `length`, and
`arithmetic` refuses the goal.

```click
theorem broken_chain(i: uint64, n: uint64, m: uint64, length: uint64) {
    requires i < n;
    requires m <= n;
    requires m <= length;
    ensures i < length by { arithmetic() using { i < n; m <= n; m <= length; } }
}
```

```expect
fail: does not follow from the listed premises' Integer readings
```
