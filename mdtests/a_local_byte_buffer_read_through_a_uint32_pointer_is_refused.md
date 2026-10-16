# A local byte buffer read through a `uint32_t *` is refused

A local `uint8_t` array's elements are character objects. A character type
may read any object, but not the reverse: a `uint32_t` read of the buffer is
refused (C11 6.5p7), as GCC at `-O2` assumes.

```c filename=bytes.c
#include <stdint.h>
uint32_t bytes(void) {
    uint8_t buf[4];
    buf[0] = 1; buf[1] = 0; buf[2] = 0; buf[3] = 0;
    const void *v = buf;
    const uint32_t *w = v;
    return *w;
}
```

```click
verifying "bytes.c";

uint32 bytes() {
    ensures true;
} by {
    execute();
}
```

```expect
fail: an object of type `char` accessed through an lvalue of type `int`
```
