# A sign conversion at 8 bits is a half-range test

Converting between `int8` and `uint8` changes no bit, so the signed
reading is negative exactly when the unsigned reading exceeds the signed
maximum `127`. `solve` proves each direction from the other, at every
width alike.

```click
theorem negative_when_above_half(u: uint8) {
    ensures u > 127 implies (u as int8) < 0;
}

theorem above_half_when_negative(u: uint8) {
    ensures (u as int8) < 0 implies u > 127;
}

theorem above_half_when_signed_negative(x: int8) {
    ensures x < 0 implies (x as uint8) > 127;
}

theorem signed_negative_when_above_half(x: int8) {
    ensures (x as uint8) > 127 implies x < 0;
}
```

```expect
pass
```
