# An unsigned order chain with an unbounded end is refused

The negative beside
`mdtests/an_unsigned_order_chain_composes_like_a_signed_one.md`. With no
bound on `n`, `x < n` says nothing about `x < 4u32`.

```click
theorem below_unbounded(x: uint32, n: uint32) {
    requires x < n;
    ensures x < 4u32 by {
        arithmetic() using {
            x < n;
        }
    }
}
```

```expect
fail: does not follow from exactly the listed arithmetic premises
```
