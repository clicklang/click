# machine integer quantified wrong signedness

```click
theorem bad(n: int8) {
    ensures exists (x: uint8) { x == x } by {
        witness(n);
        solve();
    }
}
```

```expect
fail: wrong type: expected uint8, got int8
```
