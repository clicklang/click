# A returned uint8 parameter claimed below its range is refused

A negative of `mdtests/a_returned_narrow_parameter_has_its_type_range.md`:
a `uint8` may be `255`, so `result <= 254` is refused.

```c filename=a_returned_uint8_parameter_claimed_below_its_range_is_refused.c
int32 widen_u8(uint8 x) {
    return x;
}
```

```click
verifying "a_returned_uint8_parameter_claimed_below_its_range_is_refused.c";

int32 widen_u8(uint8 x) {
    ensures result <= 254;
} by { execute(); simp(); }
```

```expect
fail: `ensures result <= 254` failed
```
