# machine specification addition needs its overflow bound

Inside `to_integer(...)`, `+` on an `int32` is the C operation, which is
undefined at `INT_MAX`, so `to_integer(x + 1) > to_integer(x)` is not proved
for every `x`. The Integer-arithmetic twin is
`mdtests/integer_arithmetic_makes_specification_addition_exact.md`.

```click
theorem signed_successor_is_greater(x: int32) {
    ensures to_integer(x + 1) > to_integer(x) by auto();
}
```

```expect
fail: x + 1
```
