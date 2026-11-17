# A `memset` declared by the built-in `<string.h>` keeps its contract

The built-in header's `memset` prototype binds to the library contract. A
fill value outside `0..=255` is accepted with C's unsigned-character conversion.

```c filename=builtin_memset.c
#include <string.h>

int fill(unsigned char *d) {
    memset(d, 300, 4);
    return 0;
}
```

```click
target "x86_64-unknown-linux-gnu";
verifying "builtin_memset.c";

int32 fill(uint8 d[]) {
    owns d[0..4];
    ensures result == 0;
}
```

```expect
pass
```
