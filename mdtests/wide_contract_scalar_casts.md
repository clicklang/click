# Native scalar casts in contracts

Contract casts name the native widening operations used by unchanged source.
An exact widening preserves a signed value, including its sign.

```click
theorem signed32(x: int32) {
    ensures to_integer(x as int128) == to_integer(x) by close();
}
theorem signed64(x: int64) {
    ensures to_integer(x as int64) == to_integer(x) by close();
    ensures to_integer(x as int128) == to_integer(x) by close();
}
theorem unsigned64(x: uint64) {
    ensures to_integer(x as uint128) == to_integer(x) by close();
    ensures to_integer(x as int128) == to_integer(x) by close();
}
```

```expect
pass
```
