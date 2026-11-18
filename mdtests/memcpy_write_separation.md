# A memcpy destination is separate from an active loan

The destination is already owned. The copy uses an entry separation fact
for its destination and the unrelated live loan. A zero-byte copy beside
a view of the same object needs no separation proof.

```c filename=memcpy_write_separation.c
#include <string.h>

void copy_beside_view(unsigned char *dst, unsigned char *src, const unsigned char *q) {
    memcpy(dst, src, 4);
}

void empty_copy_beside_view(unsigned char *q, const unsigned char *src) {
    memcpy(q, src, 0);
}
```

```click
verifying "memcpy_write_separation.c";

void copy_beside_view(uint8* dst, uint8* src, const uint8* q) {
    owns dst[0..4];
    owns src[0..4];
    views q[0..1];
    requires separate(memory(dst[0u64..4u64]), memory(q[0..1]));
    ensures click::bytes::equal(dst, 0u64, src, 0u64, 4u64);
} by {
    step() by { known(); }
}

void empty_copy_beside_view(uint8* q, const uint8* src) {
    owns q[0..1];
    views q[1..2];
    views src[0..1];
} by {
    step();
}
```

```expect
pass
```
