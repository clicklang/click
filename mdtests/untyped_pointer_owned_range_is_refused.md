# A `Pointer` range is not owned

`owns` counts a range in elements as `views` does, so
`owns (p as Pointer)[0..n]` is refused rather than owning `int32` cells
(`untyped_pointer_range_is_refused.md`). Click once accepted this contract,
counting the range as one `int32` cell at `p`.

```c filename=untyped_pointer_owned_range_is_refused.c
void clear(uint8 *p) {
    p[0] = 0;
}
```

```click
verifying "untyped_pointer_owned_range_is_refused.c";

void clear(uint8 *p) {
    owns (p as Pointer)[0..1];
    ensures p[0] == 0;
}
```

```expect
fail: a `Pointer` has no pointee type to count a range in
```
