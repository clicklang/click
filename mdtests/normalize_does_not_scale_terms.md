# Normalization checks one symbolic distribution

Explicit Integer normalization accepts one written distributivity step with
opaque operands. Full polynomial expansion still belongs to expandable search.

```click
theorem by_normalize(x: Integer, y: Integer, z: Integer) {
    ensures (x + y) * z == x * z + y * z by { normalize(); }
}
```

```expect
pass
```
