# Order spelling does not change the theorem's guarantee

```click
theorem wrong(x: uint32) {
    ensures to_integer(x) > 0 by { apply(uint32_to_integer_bounds(x)); }
}
```

```expect
fail: ended with its goal still open
```
