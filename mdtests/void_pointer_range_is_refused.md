# A `void *` range is refused

A range counts elements, and a `void *` has no element type, so
`views q[0..n]` and `owns q[0..n]` on one are refused rather than read as
`int32` cells. Click once accepted `views q[0..1]` here and then failed the
proof with "a 1-byte load at `q` did not fit the cell's value". A cast
states the element type: `views (q as (uint8 *))[0..1]`.

```c filename=void_pointer_range_is_refused.c
uint8 first(void *q) {
    return *(uint8 *)q;
}
```

```click
verifying "void_pointer_range_is_refused.c";

uint8 first(void *q) {
    views q[0..1];
    ensures result == *(q as (uint8 *));
}
```

```expect
fail: a `void *` has no pointee type to count a range in
```
