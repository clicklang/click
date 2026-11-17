# `memcpy` can overwrite a zeroed heap byte with an unwritten byte

The destination's zero initialization does not make its new bytes readable
when the corresponding source byte was unwritten.

```c filename=copy.c
#include <stdlib.h>
#include <string.h>

int answer(void) {
    unsigned char source[2];
    unsigned char *dest = calloc(2, 1);
    if (!dest) {
        return 0;
    }
    source[0] = 42;
    memcpy(dest, source, sizeof(source));
    int result = dest[1];
    free(dest);
    return result;
}
```

```click
verifying "copy.c";
int32 answer() { ensures result == result; }
```

```expect
fail:read of uninitialized storage
```
