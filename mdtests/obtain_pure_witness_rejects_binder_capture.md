# An obtained witness does not capture a universal binder

```click
theorem bound_names(x: int32) {
    requires exists (k: int32) { k == x };
    ensures forall (k: int32) { k == x } by {
        obtain (k: int32) { k == x }
        intro();
        assumption();
    }
}
```

```expect
fail: `assumption` requires the current goal as an available semantic fact
```
