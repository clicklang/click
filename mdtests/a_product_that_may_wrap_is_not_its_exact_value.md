# A product that may wrap is not its exact value

Without a bound on `x`, `x * 2u32` can wrap, so its exact value
`to_integer(x) * 2` may exceed `uint32` and the in-range identity is not
available: `auto` cannot prove the observation equal to it.

```click
theorem unbounded(x: uint32) {
    ensures to_integer(x * 2u32) == to_integer(x) * 2 by { auto(); };
}
```

```expect
fail: could not establish `to_integer((x * 2u32)) == (to_integer(x) * 2)`
```
