# A wrapped unsigned index is not kept off the cached element

`u + 1 != 0` is an Integer fact: it holds for `u == 4294967295`, where the
`unsigned` word `u + 1u` wraps to `0` and `a[u + 1u] = 1` overwrites `a[0]`.
The Integer fact must not stand in for the word disequality, so the false
claim is refused on the wrapping path.

```c filename=a_wrapped_unsigned_index_is_not_kept_off_the_cached_element.c
int read_first(unsigned u) {
    int a[8];
    a[0] = 7;
    a[u + 1u] = 1;
    int r = a[0];
    return r;
}
```

```click
verifying "a_wrapped_unsigned_index_is_not_kept_off_the_cached_element.c";

int32 read_first(uint32 u) {
    requires ((u + 1) as uint32) < 8;
    requires u + 1 != 0;
    ensures result == 7;
}
```

```expect
fail: `ensures result == 7` failed for `read_first.ensures_0`
```
