# Order spelling does not change the theorem's guarantee

```click
theorem observed_bounds(x: uint32) {
    ensures 0 <= to_integer(x);
    ensures to_integer(x) <= 4294967295;
}

theorem wrong(x: uint32) {
    ensures 0 >= to_integer(x) by apply(observed_bounds(x));
}
```

```expect
fail: ended with its goal still open
```
