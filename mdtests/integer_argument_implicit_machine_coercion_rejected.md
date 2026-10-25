# Integer theorem arguments require explicit machine observations

```click
theorem identity(n: Integer) {
    ensures n == n by solve();
}

theorem implicit_machine_argument(a: uint32) {
    ensures 0 == 0 by {
        apply(identity(a));
        solve();
    }
}
```

```expect
fail: proof step
```
