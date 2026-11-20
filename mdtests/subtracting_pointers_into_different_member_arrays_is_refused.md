# Subtracting pointers into different member arrays is refused

C defines `q - p` only when both pointers point into the same array object,
or one past its end (C11 6.5.6p9). `s->a` and `s->b` are two arrays inside
one struct. The struct is one object, but the arrays are different array
objects, so `&s->b[0] - &s->a[0]` is undefined behavior even though both
pointers lie in the same struct. Each pointer keeps its member array as its
bounds, and subtraction requires the two bounds to be the same.

```c filename=member_array_subtraction.c
struct two { int32 a[2]; int32 b[2]; };
int32 members(struct two *s) {
    int32 *p = &s->a[0];
    int32 *q = &s->b[0];
    return (int32)(q - p);
}
```

```click
verifying "member_array_subtraction.c";

int32 members(struct two *s) {
    views s->a[0..2];
    views s->b[0..2];
    ensures result == 2;
}
```

```expect
fail: pointer arithmetic left the pointed-to object
```
