# Ordering does not allow reads of uninitialized bytes

```c filename=compare.c
#include <string.h>
int ordered(void) {
    unsigned char left[1];
    unsigned char right[1] = { 2 };
    return memcmp(left, right, 1) < 0;
}
```

```click
verifying "compare.c";
int32 ordered() { ensures result == 1; }
```

```expect
fail: the caller has not initialized every byte of it
```
