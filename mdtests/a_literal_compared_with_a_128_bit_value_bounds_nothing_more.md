# A literal compared with a 128-bit value bounds nothing more

`0 < v` on an `int128` is `0 < to_integer(v)`
(`a_literal_compared_with_a_128_bit_value_takes_its_format.md`): `v` may
be `1`, so `1 < v` does not follow.

```click
theorem positive_is_not_above_one(v: int128) {
    requires 0 < v;
    ensures 1 < v;
}
```

```expect
fail: could not establish `1 < v`
```
