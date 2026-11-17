# `memcpy` can overwrite an initialized byte with an unwritten byte

The source's second byte is unwritten. The destination's old value and
initialization cannot justify reading the second byte after the copy.

```c filename=copy.c
#include <string.h>

int answer(void) {
    unsigned char source[2];
    unsigned char dest[2] = {0, 9};
    source[0] = 42;
    memcpy(dest, source, sizeof(source));
    return dest[1];
}
```

```click
verifying "copy.c";
int32 answer() { ensures result == result; }
```

```expect
fail:read of uninitialized storage
```
