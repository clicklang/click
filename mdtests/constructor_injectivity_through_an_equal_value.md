# Constructor injectivity follows through an equal value

`x` equals two `Full` constructors, so their fields are equal. Neither
constructor equality is stated directly; the equality closure joins the two
constructor applications through `x` and then joins their fields. This holds
for machine, `Integer`, and nested model fields. The refusal of a different
field position or of two unrelated values is
[`constructor_injectivity_keeps_field_positions.md`](constructor_injectivity_keeps_field_positions.md).

```click
spec enum Box { Full(int32), Empty }
spec enum Count { Count(Integer) }
spec enum Wrap { Wrap(Box) }

theorem fields_equal_through_a_shared_value(x: Box, a: int32, b: int32) {
    requires x == Box::Full(a);
    requires Box::Full(b) == x;
    ensures a == b by simp();
}

theorem integer_fields_equal_through_a_shared_value(x: Count, a: Integer, b: Integer) {
    requires x == Count::Count(a);
    requires x == Count::Count(b);
    ensures a == b by simp();
}

theorem nested_fields_equal_through_a_shared_value(x: Wrap, a: int32) {
    requires x == Wrap::Wrap(Box::Full(a));
    requires x == Wrap::Wrap(Box::Full(3));
    ensures a == 3 by simp();
}
```

```expect
pass
```
