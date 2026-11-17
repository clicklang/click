# memset does not store the unconverted int argument

The stored bytes are 44, not 300. The old range restriction is gone, but
its removal must not allow the old unconverted postcondition.

```c filename=fill_wrong.c
#include <string.h>
void fill_wrong(unsigned char *p) { memset(p, 300, 4); }
```

```click
verifying "fill_wrong.c";
void fill_wrong(uint8* p) {
    owns uninitialized(p[0u64..4u64]);
    ensures (0u64..4u64).all(|k| { p[k] == 300 });
}
```

```expect
fail: unclosed goal
```
