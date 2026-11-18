# `memcpy` replaces initialization only inside the copied span

The first source byte is written. The second is unwritten. The copy keeps
its first byte readable and leaves the destination bytes outside the copy
intact.

```c filename=copy.c
#include <string.h>

int answer(void) {
    unsigned char source[2];
    unsigned char dest[4] = {1, 2, 3, 4};
    source[0] = 42;
    memcpy(dest + 1, source, sizeof(source));
    return dest[0] + dest[1] + dest[3];
}
```

```click
verifying "copy.c";
int32 answer() { ensures result == 47; }
```

```expect
pass
```
