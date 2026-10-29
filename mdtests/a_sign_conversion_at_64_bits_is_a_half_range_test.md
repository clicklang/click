# A sign conversion at 64 bits is a half-range test

Converting between `int64` and `uint64` changes no bit, so the signed
reading is negative exactly when the unsigned reading exceeds the signed
maximum `9223372036854775807`. `solve` proves each direction from the other, at every
width alike.

```click
theorem negative_when_above_half(u: uint64) {
    ensures u > 9223372036854775807u64 implies (u as int64) < 0;
}

theorem above_half_when_negative(u: uint64) {
    ensures (u as int64) < 0 implies u > 9223372036854775807u64;
}

theorem above_half_when_signed_negative(x: int64) {
    ensures x < 0 implies (x as uint64) > 9223372036854775807u64;
}

theorem signed_negative_when_above_half(x: int64) {
    ensures (x as uint64) > 9223372036854775807u64 implies x < 0;
}
```

```expect
pass
```
