# A literal compared with a 128-bit value takes its format

An unsuffixed literal is an `int32` constant. Compared with a 64-bit value
it is converted to that value's format, as C converts it, and the same
holds against a 128-bit value: `0 < v` on an `int128` is `0i128 < v`, read
as `0 < to_integer(v)`.

`a_literal_compared_with_a_128_bit_value_bounds_nothing_more.md` is the
refused counterpart.

```click
theorem positive_is_nonnegative_int128(v: int128) {
    requires 0 < v;
    ensures 0 <= v;
}

theorem positive_is_nonnegative_uint128(v: uint128) {
    requires 0 < v;
    ensures 0 <= v;
    ensures v != 0;
}

theorem shifted_bound_int128(v: int128) {
    requires 5 < v;
    ensures 4 < v;
    ensures v > -3;
}
```

```expect
pass
```
