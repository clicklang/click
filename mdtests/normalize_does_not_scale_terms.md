# Normalization keeps symbolic products opaque

Explicit Integer normalization distributes constant coefficients, but not a
product of two symbolic operands. Such a product still needs its named law
or arithmetic proof search.

```click
theorem by_arithmetic(x: Integer, y: Integer, z: Integer) {
    ensures (x + y) * z == x * z + y * z by { solve() using {}; }
}

theorem by_normalize(x: Integer, y: Integer, z: Integer) {
    ensures (x + y) * z == x * z + y * z by { normalize(); }
}
```

```expect
fail: `normalize` goal did not normalize to true
```
