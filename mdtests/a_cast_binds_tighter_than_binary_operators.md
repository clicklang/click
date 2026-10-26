# A cast binds tighter than binary operators and looser than unary ones

`a as int64 + b as int64` adds two widened values, `-x as uint64` widens the
`uint32` negation, and `x as uint32 as int32` applies the casts left to right
(`docs/reference/language/index.md`, Casts).

```click
theorem widened_sum(a: uint32, b: uint32) {
    requires to_integer(a) + to_integer(b) <= 4294967295;
    ensures a as int64 + b as int64 <= 4294967295i64;
}

theorem widened_negation(x: uint32) {
    requires x == 1u32;
    ensures -x as uint64 == 4294967295u64;
}

theorem round_trip(x: int32) {
    requires 0 <= x;
    ensures x as uint32 as int32 == x;
}
```

```expect
pass
```
