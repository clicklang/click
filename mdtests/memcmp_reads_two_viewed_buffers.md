# memcmp reads two viewed buffers, or one buffer twice

The standard-library `memcmp` contract views both operands. Two views compose
(`compare_two`), and one viewed range serves as both operands at once
(`compare_self`): views are shared, so lending the same bytes twice to one
call is not an overlap.

```c filename=memcmp_reads_two_viewed_buffers.c
#include <string.h>
int compare_two(const unsigned char *a, const unsigned char *b) {
    return memcmp(a, b, 4);
}
int compare_self(const unsigned char *a) {
    return memcmp(a, a, 4);
}
```

```click
verifying "memcmp_reads_two_viewed_buffers.c";
int32 compare_two(const uint8* a, const uint8* b) {
    views a[0..4];
    views b[0..4];
    requires forall (k: uint64) { k < 4u64 implies defined(a[k]) and defined(b[k]) };
    ensures result == 0 implies click::bytes::equal(a, 0u64, b, 0u64, 4u64);
} by { execute(); simp(); }

int32 compare_self(const uint8* a) {
    views a[0..4];
    requires forall (k: uint64) { k < 4u64 implies defined(a[k]) };
    ensures result == 0 implies click::bytes::equal(a, 0u64, a, 0u64, 4u64);
} by { execute(); simp(); }
```

```expect
pass
```
