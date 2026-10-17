# auto reads a definedness premise as Integer bounds

`defined(a + b)` on `int32` holds exactly when the exact sum
`to_integer(a) + to_integer(b)` lies in the `int32` range, so `auto` may read
the premise as those two bounds, for a variable or a constant operand. With
them it proves a bound on the sum and the in-range identity
`to_integer(a + b) == to_integer(a) + to_integer(b)`,
which `pool_grow` in `examples/bounded-pool` needs after its C update
`pool->capacity = pool->capacity + amount`.

```click
arithmetic "integer";

theorem a_defined_sum_is_bounded(a: int32, b: int32) {
    requires defined(a + b);
    ensures to_integer(a) + to_integer(b) <= 2147483647 by auto();
}

theorem a_defined_sum_is_its_integer_sum(a: int32, b: int32) {
    requires defined(a + b);
    ensures to_integer(a + b) == to_integer(a) + to_integer(b) by auto();
}

theorem a_defined_increment_is_its_integer_increment(a: int32) {
    requires defined(a + 1);
    ensures to_integer(a + 1) == to_integer(a) + 1 by auto();
}

theorem a_defined_difference_is_its_integer_difference(a: int32, b: int32) {
    requires defined(a - b);
    ensures to_integer(a - b) == to_integer(a) - to_integer(b) by auto();
}
```

```expect
pass
```
