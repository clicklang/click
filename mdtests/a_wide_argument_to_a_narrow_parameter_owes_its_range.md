# A wide argument to a narrow parameter owes its range

The caller's side of
`mdtests/a_narrow_parameter_has_its_type_range_at_entry.md`. `widen` assumes
its `uint8` parameter is in `[0, 255]`; that is sound because every call
converts its argument to `uint8`, and the conversion owes the range. An
unbounded `int32` argument cannot show it, so the call is refused.
`mdtests/a_bounded_argument_to_a_narrow_parameter_is_in_its_range.md` is the
positive.

```c filename=a_wide_argument_to_a_narrow_parameter_owes_its_range.c
int32 widen(uint8 x) {
    return x;
}

int32 pass_wide(int32 y) {
    return widen(y);
}
```

```click
verifying "a_wide_argument_to_a_narrow_parameter_owes_its_range.c";

int32 widen(uint8 x) {
    ensures result >= 0;
    ensures result <= 255;
} by { execute(); simp(); }

int32 pass_wide(int32 y) {
    ensures result >= 0;
    ensures result <= 255;
} by { execute(); simp(); }
```

```expect
fail: missing prerequisite (uint8 narrowing lower bound)
```
