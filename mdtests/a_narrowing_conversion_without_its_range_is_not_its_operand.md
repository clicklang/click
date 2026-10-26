# A narrowing conversion without its range is not its operand

A negative of
[`auto_widens_a_narrow_value_into_a_containing_type.md`](auto_widens_a_narrow_value_into_a_containing_type.md).
`(signed char)x` of an `int` wraps outside `signed char`'s range, so without
a range on `x` its value need not be `x`'s.

```c filename=not_widen.c
signed char narrow(int x) { return (signed char)x; }
```

```click
verifying "not_widen.c";

signed char narrow(int x) {
    ensures to_integer(result) == to_integer(x);
} by { execute(); solve(); }
```

```expect
fail: did not retain a complete proof for `narrow.ensures_0`
```
