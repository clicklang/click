# A sign conversion is not negative below the half

The signed reading of an unsigned value is negative exactly when the value
exceeds the signed maximum. One below that boundary is not enough: `127` read
as an `int8` is `127`.

```click
theorem negative_one_below_half(u: uint8) {
    ensures u > 126 implies (u as int8) < 0;
}
```

```expect
fail: `solve` failed for `negative_one_below_half.ensures_0`
```
