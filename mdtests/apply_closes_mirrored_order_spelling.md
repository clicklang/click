# `apply` closes a goal spelled from the other side of its conclusion

`a <= b` and `b >= a` are one order claim, and so are `a < b` and `b > a`.
A theorem conclusion closes the goal under either spelling, for the
mathematical `Integer` order and for signed and unsigned machine orders. Each
pair below applies one theorem to the goal written both ways; the first
spelling of every pair matches the theorem's own, the second is mirrored.

```click
import click::integer;
theorem observed_range(value: uint32) {
    ensures 0 <= to_integer(value);
    ensures to_integer(value) >= 0;
    ensures to_integer(value) <= 4294967295;
    ensures 4294967295 >= to_integer(value);
}

theorem integer_successor_is_greater(value: Integer) {
    ensures value < value + 1 by solve();
}

theorem strict_integer_order(value: Integer) {
    ensures value < value + 1 by apply(integer_successor_is_greater(value));
    ensures value + 1 > value by apply(integer_successor_is_greater(value));
}

theorem strict_signed_order(value: int32) {
    requires value < 100;
    ensures to_integer(value) < to_integer(value + 1);
    ensures to_integer(value + 1) > to_integer(value);
}

theorem unsigned_order(value: uint32, upper: uint32) {
    requires value < upper;
    ensures to_integer(value + 1u32) <= to_integer(upper);
    ensures to_integer(upper) >= to_integer(value + 1u32);
}
```

```expect
pass
```
