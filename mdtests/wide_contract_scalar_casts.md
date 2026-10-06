# Native scalar casts in contracts

Contract casts name the native widening operations used by unchanged source.
An exact widening preserves a signed value, including its sign.

```click
theorem signed32(x: int32) {
    ensures to_integer((int128)x) == to_integer(x) by simp;
}
theorem signed64(x: int64) {
    ensures to_integer((int64)x) == to_integer(x) by simp;
    ensures to_integer((int128)x) == to_integer(x) by simp;
}
theorem unsigned64(x: uint64) {
    ensures to_integer((uint128)x) == to_integer(x) by simp;
    ensures to_integer((int128)x) == to_integer(x) by simp;
}
```

```expect
pass
```
