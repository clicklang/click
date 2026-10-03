# A returned narrow parameter has its type range

A `uint8` is in `[0, 255]`, and returning it as `int32` keeps that range.
The range is an entry fact of the function
(`mdtests/a_narrow_parameter_has_its_type_range_at_entry.md`), so `return x;`
reaches the claim with it, though the return conversion widens the value
without restating anything.
`mdtests/a_returned_uint8_parameter_claimed_below_its_range_is_refused.md` and
`mdtests/a_returned_int8_parameter_claimed_above_its_lower_bound_is_refused.md`
are the negatives.

```c filename=a_returned_narrow_parameter_has_its_type_range.c
int32 widen_u8(uint8 x) {
    return x;
}

int32 widen_u16(uint16 x) {
    return x;
}

int32 widen_i8(int8 x) {
    return x;
}

int32 widen_i16(int16 x) {
    return x;
}
```

```click
verifying "a_returned_narrow_parameter_has_its_type_range.c";

int32 widen_u8(uint8 x) {
    ensures result >= 0;
    ensures result <= 255;
} by { execute(); simp(); }

int32 widen_u16(uint16 x) {
    ensures result >= 0;
    ensures result <= 65535;
} by { execute(); simp(); }

int32 widen_i8(int8 x) {
    ensures result >= -128;
    ensures result <= 127;
} by { execute(); simp(); }

int32 widen_i16(int16 x) {
    ensures result >= -32768;
    ensures result <= 32767;
} by { execute(); simp(); }
```

```expect
pass
```
