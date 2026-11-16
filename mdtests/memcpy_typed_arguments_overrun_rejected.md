# Native memory arguments do not grant access beyond their objects

The implicit byte view used for a library call grants no additional storage
or permissions. Both scalar objects are four bytes; a five-byte copy must
still be refused.

```c filename=overrun.c
#include <stdint.h>
#include <string.h>

uint32_t overrun(uint32_t value) {
    uint32_t out;
    memcpy(&out, &value, sizeof(out) + 1);
    return out;
}
```

```click
verifying "overrun.c";

uint32_t overrun(uint32_t value) {
    ensures result == value;
}
```

```expect
fail: missing resource fact `owns out[0..5]`
```
