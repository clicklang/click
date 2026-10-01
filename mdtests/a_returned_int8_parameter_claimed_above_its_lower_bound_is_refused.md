# A returned int8 parameter claimed above its lower bound is refused

A negative of `mdtests/a_returned_narrow_parameter_has_its_type_range.md`:
an `int8` may be `-128`, so `result >= -127` is refused.

```c filename=a_returned_int8_parameter_claimed_above_its_lower_bound_is_refused.c
int32 widen_i8(int8 x) {
    return x;
}
```

```click
verifying "a_returned_int8_parameter_claimed_above_its_lower_bound_is_refused.c";

int32 widen_i8(int8 x) {
    ensures result >= -127;
} by { execute(); simp(); }
```

```expect
fail: `ensures result >= -127` failed
```
