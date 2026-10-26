# a pure conditional with bounded arms has an interval

An indicator `if c { 1 } else { 0 }` denotes one of its two arms, so the hull
of the arms' intervals bounds it. Both int32 bounds close by `simp`. The
`to_integer` forms carry those bounds across the conversion with the existing
`integer::int32_less_equal_to_integer` law; the conversion itself is unchanged.

```click
import click::integer;

theorem indicator_is_nonnegative(x: int32) {
    ensures 0 <= if x == 0 { 1 } else { 0 } by {
        solve();
    }
}

theorem indicator_is_at_most_one(x: int32) {
    ensures if x == 0 { 1 } else { 0 } <= 1 by {
        solve();
    }
}

theorem indicator_integer_is_nonnegative(x: int32) {
    ensures 0 <= to_integer(if x == 0 { 1 } else { 0 }) by {
        have 0 <= if x == 0 { 1 } else { 0 };
        have to_integer(0) <= to_integer((if x == 0 { 1 } else { 0 })) by auto();
        solve();
    }
}

theorem indicator_integer_is_at_most_one(x: int32) {
    ensures to_integer(if x == 0 { 1 } else { 0 }) <= 1 by {
        have if x == 0 { 1 } else { 0 } <= 1;
        have to_integer((if x == 0 { 1 } else { 0 })) <= to_integer(1) by auto();
        solve();
    }
}
```

```expect
pass
```
