# Subtracting pointers into one member array is accepted

The same-array rule for `q - p` (C11 6.5.6p9) is about the array, not the
struct: two pointers into the member array `s->a`, including its one-past
end, may be subtracted. Contrast
[different member arrays](subtracting_pointers_into_different_member_arrays_is_refused.md).

```c filename=one_member_array_subtraction.c
struct two { int32 a[2]; int32 b[2]; };
int32 same_member(struct two *s) {
    int32 *p = &s->a[0];
    int32 *q = s->a + 2;
    return (int32)(q - p);
}
```

```click
verifying "one_member_array_subtraction.c";

int32 same_member(struct two *s) {
    views s->a[0..2];
    ensures result == 2;
}
```

```expect
pass
```
