# A polynomial node rejects a false successor coefficient

```click
theorem false_successor(n: Integer) {
    ensures (n + 1) * (n + 2) == n * (n + 1) + 3 * (n + 1) by {
        close() using {  };
    }
}
```

```expect
fail: solve
```
