# A `char *` argument to a byte predicate unfolds to the same byte reads

`bytes::equal` reads `uint8` bytes. A `char *` argument is passed as its
explicit byte view, so the call's `memcpy` postcondition and the caller's
written postcondition are one instance. Unfolding the caller's goal reads the
same `uint8` loads the call's fact does, not `(int8)` conversions of them, so
`copy_c` verifies exactly as `copy_u` does.

```c filename=c.c
#include <string.h>
void copy_u(unsigned char *dst, const unsigned char *src) { memcpy(dst, src, 4); }
void copy_c(char *dst, const char *src) { memcpy(dst, src, 4); }
```

```click
import click::bytes;
verifying "c.c";
void copy_u(uint8* dst, const uint8* src) {
    views src[0..4];
    owns dst[0..4];
    ensures bytes::equal(dst, 0u64, src, 0u64, 4u64);
} by { execute(); simp(); }
void copy_c(char* dst, const char* src) {
    views src[0..4];
    owns dst[0..4];
    ensures bytes::equal(dst, 0u64, src, 0u64, 4u64);
} by { execute(); simp(); }
```

```expect
pass
```
