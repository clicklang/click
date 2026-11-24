# A `Pointer` range is refused

A range counts elements, and a `Pointer` has no element type, so
`views (p as Pointer)[0..n]` is refused rather than read as `int32` cells,
as a `void *` range is (`void_pointer_range_is_refused.md`). Click once
accepted this `views` as one `int32` cell at `p` and then failed the proof
with "a 1-byte load at `p` did not fit the cell's value". A typed pointer
states the element type: `views p[0..1]`.

```c filename=untyped_pointer_range_is_refused.c
uint8 first(uint8 *p) {
    return p[0];
}
```

```click
verifying "untyped_pointer_range_is_refused.c";

uint8 first(uint8 *p) {
    views (p as Pointer)[0..1];
    ensures result == p[0];
}
```

```expect
fail: a `Pointer` has no pointee type to count a range in
```
