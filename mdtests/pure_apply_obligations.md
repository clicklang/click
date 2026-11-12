# Applying a named theorem exposes its premises as obligations

```click
theorem nonnegative(n: Integer) {
    requires n >= 0;
    ensures n >= 0 by assumption();
}
theorem positive(n: Integer) {
    requires n > 0;
    ensures n >= 0 by {
        apply(nonnegative(n));
    }
}
```

```expect
pass
```
