# An int8 parameter claimed above its lower bound at entry is refused

A negative of `mdtests/a_narrow_parameter_has_its_type_range_at_entry.md`:
an `int8` may be `-128`, so `x >= -127` is refused.

```c filename=an_int8_parameter_claimed_above_its_lower_bound_at_entry_is_refused.c
int32 ignore_i8(int8 x) {
    return 0;
}
```

```click
verifying "an_int8_parameter_claimed_above_its_lower_bound_at_entry_is_refused.c";

int32 ignore_i8(int8 x) {
    ensures x >= -127;
} by { execute(); simp(); }
```

```expect
fail: `ensures x >= -127` failed
```
