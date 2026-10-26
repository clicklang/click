# Exact Integer successor

The claim holds for every mathematical integer, including values at and
beyond machine limits. It needs no signed-overflow premise.

```click
theorem integer_successor(z: Integer) {
    ensures z + 1 > z by {
        solve();
    }
}
```

```expect
pass
```
