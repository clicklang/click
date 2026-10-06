# Opaque arithmetic retains its exact terms and evaluation guards

```click
theorem unguarded(n: Integer, d: Integer) {
    ensures truncating_quotient(n, d) - truncating_quotient(n, d) == 0 by { arithmetic(); }
}
```

```expect
fail: it denotes a value only where 1 condition of its evaluation holds
```
