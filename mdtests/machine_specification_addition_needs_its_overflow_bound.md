# machine specification addition needs its overflow bound

Without `arithmetic "integer";`, specification `+` on an `int32` is the C
operation, which is undefined at `INT_MAX`, so `x + 1 > x` is not proved
for every `x`. The Integer-arithmetic twin is
`mdtests/integer_arithmetic_makes_specification_addition_exact.md`.

```click
theorem signed_successor_is_greater(x: int32) {
    ensures x + 1 > x by auto();
}
```

```expect
fail: x + 1
```
