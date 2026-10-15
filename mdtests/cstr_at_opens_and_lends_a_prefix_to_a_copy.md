# A borrowed C string opens and lends a prefix of its bytes

`copy_prefix` borrows `cstr_at(src, n)`, the `n + 1` bytes of `src` through
its terminator with all four facts that make them the C string of length `n`.
It opens the composite and passes the first `k` bytes, for `k <= n`, to a
`memcpy`-style copy whose contract views only `source[0..k]`. The opened view
covers that prefix, and the string's facts are available inside the scope.

```c filename=cstr_at_opens_and_lends_a_prefix_to_a_copy.c
uint8 *copy_bytes(uint8 *destination, const uint8 *source, uint64 bytes);

uint64 copy_prefix(uint8 *dst, const uint8 *src, uint64 n, uint64 k)
{
	copy_bytes(dst, src, k);
	return k;
}
```

```click
// The resource proposed for `library/cstr.click`, declared here because a
// library module cannot yet export a composite resource: a view of the bytes
// of `p` through its first terminator, with the facts that make them the C
// string of length `len`.
resource cstr_at(p: const uint8*, len: uint64) {
    views p[0..len + 1u64];
    fact len < 18446744073709551615u64;
    fact forall (k: uint64) { 0u64 <= k and k < len implies p[k] != '\0' };
    fact p[len] == '\0';
    fact forall (k: uint64) { 0u64 <= k and k < len + 1u64 implies defined(p[k]) };
}

verifying "cstr_at_opens_and_lends_a_prefix_to_a_copy.c";

extern uint8* copy_bytes(uint8 destination[], const uint8 source[], uint64 bytes) {
    views source[0..bytes];
    owns destination[0..bytes];
    ensures result == destination;
}

uint64 copy_prefix(uint8* dst, const uint8* src, uint64 n, uint64 k) {
    views cstr_at(src, n);
    requires k <= n;
    owns dst[0..k];
    ensures result == k;
    ensures src[n] == '\0';
} by {
    open(cstr_at(src, n)) {
        execute();
        simp();
    }
}
```

```expect
pass
```
