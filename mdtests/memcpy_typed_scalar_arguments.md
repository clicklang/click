# memcpy accepts the native addresses of scalar objects

The C library declares both memory arguments as `void *` views. Copying an
object into another object of its type needs no byte-pointer casts in C.
The result must preserve every bit of the input, including symbolic values.

```c filename=copy_u32.c
#include <stdint.h>
#include <string.h>

uint32_t copy_u32(uint32_t value) {
    uint32_t out;
    memcpy(&out, &value, sizeof(out));
    return out;
}

struct pair {
    uint32_t left;
    uint32_t right;
};

uint32_t copy_field(uint32_t value) {
    struct pair source = {0, value};
    uint32_t out;
    memcpy(&out, &source.right, sizeof(out));
    return out;
}
```

```click
verifying "copy_u32.c";

uint32_t copy_u32(uint32_t value) {
    ensures result == value;
}

uint32_t copy_field(uint32_t value) {
    ensures result == value;
}
```

```expect
pass
```
