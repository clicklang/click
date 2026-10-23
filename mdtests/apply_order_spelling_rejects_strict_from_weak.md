# Order spelling does not change the theorem's guarantee

```click
theorem observed_bounds(x: uint32) {
    ensures 0 <= to_integer(x) by auto();
    ensures to_integer(x) <= 4294967295 by auto();
}

theorem wrong(x: uint32) {
    ensures to_integer(x) > 0 by apply(observed_bounds(x));
}
```

```expect
fail: ended with its goal still open
```
