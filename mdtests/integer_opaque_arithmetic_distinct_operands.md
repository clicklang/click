# Opaque arithmetic retains its exact terms and evaluation guards

```click
theorem false_substitution(a: Integer, b: Integer, c: Integer) {
    requires a * b <= 0;
    ensures a * c <= 0 by { arithmetic() using { a * b <= 0; } }
}
```

```expect
fail: no combination of the listed premises proves it
```
