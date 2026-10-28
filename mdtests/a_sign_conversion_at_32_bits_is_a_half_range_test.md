# A sign conversion at 32 bits is a half-range test

Converting between `int32` and `uint32` changes no bit, so the signed
reading is negative exactly when the unsigned reading exceeds the signed
maximum `2147483647`. `solve` proves each direction from the other, at every
width alike.

```click
theorem negative_when_above_half(u: uint32) {
    ensures u > 2147483647u32 implies (u as int32) < 0;
}

theorem above_half_when_negative(u: uint32) {
    ensures (u as int32) < 0 implies u > 2147483647u32;
}

theorem above_half_when_signed_negative(x: int32) {
    ensures x < 0 implies (x as uint32) > 2147483647u32;
}

theorem signed_negative_when_above_half(x: int32) {
    ensures (x as uint32) > 2147483647u32 implies x < 0;
}
```

```expect
pass
```
