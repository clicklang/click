# Normalization keeps symbolic products opaque

Explicit Integer normalization distributes constant coefficients, but not a
product of two symbolic operands. A symbolic product stays opaque even when distribution is mathematically valid.

```click
theorem by_normalize(x: Integer, y: Integer, z: Integer) {
    ensures (x + y) * z == x * z + y * z by { normalize(); }
}
```

```expect
fail: `normalize` goal did not normalize to true
```
