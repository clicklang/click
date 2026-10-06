# Opaque arithmetic retains its exact terms and evaluation guards

```click
theorem false_product(a: Integer, b: Integer) {
    requires a <= 0;
    requires b <= 0;
    ensures a * b <= 0 by { arithmetic() using { a <= 0; b <= 0; } }
}
```

```expect
fail: no combination of the listed premises proves it
```
