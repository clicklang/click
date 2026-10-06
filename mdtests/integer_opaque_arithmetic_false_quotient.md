# Opaque arithmetic retains its exact terms and evaluation guards

```click
theorem false_quotient(n: Integer, d: Integer) {
    requires d != 0;
    ensures truncating_quotient(n, d) == 1 by { arithmetic(); }
}
```

```expect
fail: no combination of the listed premises proves it
```
