# Pointer arithmetic past a viewed range of a parameter is refused

C11 6.5.6p8 defines `p + k` only for a result inside the array object or one
past its end. A pointer parameter has no recorded object size; the `views`
range the function holds is the only extent Click knows for it, so `p + 1000`
under `views p[0..4]` leaves every range the state holds. The formation is
refused where it happens, not only when the displaced pointer is read: here it
is never dereferenced, only compared, which previously decided `q != p`.

```c filename=pointer_arithmetic_past_a_viewed_range_is_refused.c
int32 f(int32 *p) { int32 *q = p + 1000; return q != p; }
```

```click
verifying "pointer_arithmetic_past_a_viewed_range_is_refused.c";

int32 f(int32 *p) {
    views p[0..4];
    ensures result == 1;
} by { execute(); simp(); }
```

```expect
fail: pointer arithmetic left the pointed-to object
```
