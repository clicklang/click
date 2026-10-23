# arithmetic using gives a signed value no zero floor

A signed value may be negative, so `k < x` with `x == 0` is consistent and
`arithmetic() using` does not prove `false` from it. Only an unsigned range
makes that pair a contradiction.

```click
theorem below_zero_is_consistent(k: int32, x: int32) {
    requires k < x;
    requires x == 0;
    ensures false by { arithmetic() using { k < x; x == 0; }; }
}
```

```expect
fail: no combination of the listed premises proves it
```
