# Converting a memset fill value does not grant write permissions

A negative fill value is valid, but a five-byte fill still requires five
writable bytes. The caller owns only four.

```c filename=overfill.c
#include <string.h>
void overfill(unsigned char *p) { memset(p, -1, 5); }
```

```click
verifying "overfill.c";
void overfill(uint8* p) {
    owns p[0..4];
    ensures true;
}
```

```expect
fail: missing resource fact `owns p[0..5]`
```
