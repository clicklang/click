# Integer coefficient identities

The proof is context-free and preserves nonlinear products as opaque atoms.

```click
theorem coefficients(x: Integer, y: Integer) {
    ensures 3 * (x - y) == x + x + x - 3 * y by { close(); }
    ensures (2 + 3) * x == 5 * x by { close(); }
    ensures -2 * (x + y) + 2 * y == -2 * x by { close(); }
    ensures 2 * (x * y) == x * y + x * y by { close(); }
}
```

```expect
pass
```
