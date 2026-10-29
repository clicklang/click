# A sign conversion at 16 bits is a half-range test

Converting between `int16` and `uint16` changes no bit, so the signed
reading is negative exactly when the unsigned reading exceeds the signed
maximum `32767`. `solve` proves each direction from the other, at every
width alike.

```click
theorem negative_when_above_half(u: uint16) {
    ensures u > 32767 implies (u as int16) < 0;
}

theorem above_half_when_negative(u: uint16) {
    ensures (u as int16) < 0 implies u > 32767;
}

theorem above_half_when_signed_negative(x: int16) {
    ensures x < 0 implies (x as uint16) > 32767;
}

theorem signed_negative_when_above_half(x: int16) {
    ensures (x as uint16) > 32767 implies x < 0;
}
```

```expect
pass
```
