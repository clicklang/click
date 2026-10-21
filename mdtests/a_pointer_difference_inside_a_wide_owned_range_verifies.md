# A pointer difference inside a wide owned range verifies

`p - dst` subtracts two pointers into the same buffer, and `owns dst[0..osz]` with a `uint64` length with `osz > 0` is the only evidence that `dst` points into an object. That ownership records a wide (64-bit count) loadability fact. The object-provenance check read every loadability fact for the object as a 32-bit count and panicked on the wide one; it now reads a wide count as unsigned 64 bits. The source is reduced from `string_escape_mem` in Linux `lib/string_helpers.c`, which returns `p - dst`.

```c filename=wide_difference.c
int f(char *dst, unsigned long osz)
{
	char *p = dst;
	return p - dst;
}
```

```click
verifying "wide_difference.c";

int32 f(char *dst, uint64 osz) {
    requires osz > 0;
    owns dst[0..osz];
    ensures result == 0;
} by {
    execute();
    simp();
}
```

```expect
pass
```
