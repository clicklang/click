# A pass-through call returns its allocation cleanup authority

The callee returns the allocation it consumed through an equal result pointer.
Its resource token and existing cleanup anchor return together: both 32-bit
and size_t sizes remain live, and the caller can free the returned alias.
No population resource is involved. Before, the heap checker retained the
allocation while the companion ledger lost its alias and refused the call.

```c filename=pass_through.c
#include <stdint.h>
#include <stddef.h>
#include <stdlib.h>

uint32_t *pass32(uint32_t *p, int n) { return p; }
int caller32(int n) {
    uint32_t *p = malloc(n * 4);
    if (p == 0) return 0;
    uint32_t *q = pass32(p, n);
    free(q);
    return 1;
}

uint32_t *pass64(uint32_t *p, size_t n) { return p; }
int caller64(size_t n) {
    uint32_t *p = malloc(n * sizeof(uint32_t));
    if (p == 0) return 0;
    uint32_t *q = pass64(p, n);
    free(q);
    return 1;
}
```

```click
verifying "pass_through.c";

uint32_t* pass32(uint32_t* p, int32 n) {
    requires 1 <= n and n <= 1000;
    consumes allocation(p, n * 4);
    consumes uninitialized(p[0..n]);
    ensures result == p;
    produces allocation(result, n * 4);
    produces uninitialized(result[0..n]);
}
int32 caller32(int32 n) {
    requires 1 <= n and n <= 1000;
    ensures result == 0 or result == 1;
}

uint32_t* pass64(uint32_t* p, size_t n) {
    requires 1u64 <= n and n <= 1000u64;
    consumes allocation(p, n * 4u64);
    consumes uninitialized(p[0..n]);
    ensures result == p;
    produces allocation(result, n * 4u64);
    produces uninitialized(result[0..n]);
}
int32 caller64(size_t n) {
    requires 1u64 <= n and n <= 1000u64;
    ensures result == 0 or result == 1;
}
```

```expect
pass
```
