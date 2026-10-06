# Integer theorem arguments require explicit machine observations

```click
theorem identity(n: Integer) {
    ensures n == n by { simp(); }
}

theorem implicit_machine_argument(a: uint32) {
    ensures 0 == 0 by {
        apply(identity(a));
        simp();
    }
}
```

```expect
fail: proof step
```
