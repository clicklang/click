# A uint8 parameter claimed below its range at entry is refused

A negative of `mdtests/a_narrow_parameter_has_its_type_range_at_entry.md`:
a `uint8` may be `255`, so `x <= 254` is refused.

```c filename=a_uint8_parameter_claimed_below_its_range_at_entry_is_refused.c
int32 ignore_u8(uint8 x) {
    return 0;
}
```

```click
verifying "a_uint8_parameter_claimed_below_its_range_at_entry_is_refused.c";

int32 ignore_u8(uint8 x) {
    ensures x <= 254;
} by { execute(); simp(); }
```

```expect
fail: `ensures x <= 254` failed
```
