# An instantiated machine requirement keeps its observations

The pure application proves the native comparison of the wrapping uint64
difference. Its obligation must retain `to_integer(n - k)`, rather than
turning the argument into unbounded subtraction.

```click
theorem big(a: uint64) {
    requires 100u64 < a;
    ensures true by { solve(); }
}

theorem wrapped(n: uint64, k: uint64) {
    requires n == 5u64;
    requires k == 30u64;
    ensures true by {
        apply(big(n - k));
        solve();
    }
}
```

```expect
pass
```
