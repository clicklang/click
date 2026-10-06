# Casts preserve their native signedness

A same-width signed-to-unsigned cast does not preserve a negative Integer.

```click
theorem wrong(x: int128) {
    requires to_integer(x) == -1;
    ensures to_integer((uint128)x) == -1 by simp;
}
```

```expect
fail: could not establish
```
