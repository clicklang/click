# Opaque arithmetic retains its exact terms and evaluation guards

```click
theorem false_quotient(n: Integer, d: Integer) {
    requires d != 0;
    ensures truncating_quotient(n, d) == 1 by arithmetic();
}
```

```expect
fail: `arithmetic` read the current goal as an Integer linear claim, which does not hold on its own
```
