# A pointer difference over an empty wide owned range needs a nonnull base

An empty `owns dst[0..osz]` range, a `uint64` length that may be `0`, is no evidence that `dst` points into an object, so `p - dst` is refused as pointer arithmetic that left its object (the unproved goal is `dst != 0`). Before the wide-count fix this source panicked; see `a_pointer_difference_inside_a_wide_owned_range_verifies.md`.

```c filename=wide_empty_difference.c
int f(char *dst, unsigned long osz)
{
	char *p = dst;
	return p - dst;
}
```

```click
verifying "wide_empty_difference.c";

int32 f(char *dst, uint64 osz) {
    owns dst[0..osz];
    ensures result == 0;
} by {
    execute();
    simp();
}
```

```expect
fail: pointer arithmetic left the pointed-to object
```
