# Distinct constructors of one value are a contradiction

`x` equals both `Full(a)` and `Empty`. Neither equality between the two
constructors is stated; the equality closure joins them through `x`, and two
variants in one class make the context impossible. The nested case joins
`Full(a)` and `Empty` as fields of one `Wrap`.

```click
spec enum Box { Full(int32), Empty }
spec enum Wrap { Wrap(Box) }

theorem distinct_variants_through_a_shared_value(x: Box, a: int32) {
    requires x == Box::Full(a);
    requires x == Box::Empty;
    ensures 0 == 1 by assumption();
}

theorem distinct_nested_variants_through_a_shared_value(x: Wrap, a: int32) {
    requires x == Wrap::Wrap(Box::Full(a));
    requires Wrap::Wrap(Box::Empty) == x;
    ensures 0 == 1 by simp();
}
```

```expect
pass
```
