# A `bool` cell is not copied into as bytes

A `bool` object's byte is 1 or 0. `memcpy` from another object could copy
any byte into it, so a byte copy into a `bool` object is refused.

```c filename=bool_memcpy.c
#include <stdbool.h>
#include <string.h>

bool copied(void) {
    bool b = false;
    unsigned char x = 2;
    memcpy(&b, &x, 1);
    return b;
}
```

```click
verifying "bool_memcpy.c";

Bool copied() {
    ensures result;
}
```

```expect
fail: `step()` could not verify C operation: type mismatch
```
