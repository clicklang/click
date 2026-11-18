# `memcpy` preserves initialization when the source value is unknown

The call may change `source[0]`, which has been initialized. `memcpy`
copies it into a fresh destination, leaving it readable there.

```c filename=copy.c
#include <string.h>

void change(unsigned char *p);

int answer(void) {
    unsigned char source[2];
    unsigned char dest[2];
    source[0] = 42;
    change(source);
    memcpy(dest, source, sizeof(source));
    return dest[0];
}
```

```click
verifying "copy.c";
extern void change(uint8* p) { owns p[0..1]; }
int32 answer() { ensures result == result; }
```

```expect
pass
```
