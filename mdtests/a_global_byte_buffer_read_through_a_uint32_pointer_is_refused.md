# A global byte buffer read through a `uint32_t` pointer is refused

The elements of a global `uint8_t` array are character objects, which a
`uint32_t` lvalue may not read (C11 6.5p7).

```c filename=globals.c
#include <stdint.h>
uint8_t buffer[4];

uint32_t read_buffer(void) {
    void *v = buffer;
    uint32_t *w = v;
    return *w;
}
```

```click
verifying "globals.c";

uint32 read_buffer() {
    owns buffer[0..4];
    ensures true;
} by {
    execute();
}
```

```expect
fail: an object of type `char` accessed through an lvalue of type `int`
```
