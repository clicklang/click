# A byte buffer read through a `uint32_t` pointer is refused

A character type may read any object, but the reverse does not hold: an array
of `uint8_t` is an object of character type, and reading it through a
`uint32_t *` is an access through an incompatible type (C11 6.5p7). GCC at
`-O2` may reorder such a read across stores to the buffer, so it is refused;
copy the bytes with `memcpy` instead.

```c filename=load32.c
#include <stdint.h>

uint32_t load32(const uint8_t *buf) {
    return *(const uint32_t *)(const void *)buf;
}
```

```click
verifying "load32.c";

uint32 load32(const uint8* buf) {
    requires buf != 0;
    views buf[0u64..4u64];
    ensures true;
} by {
    execute();
    simp();
}
```

```expect
fail: an object of type `char` accessed through an lvalue of type `int`
```
