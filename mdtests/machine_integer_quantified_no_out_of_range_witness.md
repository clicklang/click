# machine integer quantified no out of range witness

```click
theorem bad() {
    ensures exists (x: uint8) { x == 300 } by solve();
}
```

```expect
fail: could not establish
```
