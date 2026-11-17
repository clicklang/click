# memset converts every int fill value to unsigned char

The C source uses ordinary `memset` calls. Its fill argument is an `int`,
but the stored value is its unsigned-character conversion, including for
negative values and values greater than 255. The length is symbolic.

```c filename=fill.c
#include <stddef.h>
#include <string.h>

void fill_ff(unsigned char *p, size_t n) {
    memset(p, -1, n);
}

void fill_300(unsigned char *p, size_t n) {
    memset(p, 300, n);
}

void fill_any(unsigned char *p, int value, size_t n) {
    memset(p, value, n);
}
```

```click
verifying "fill.c";

void fill_ff(uint8* p, size_t n) {
    requires n <= 1024u64;
    owns uninitialized(p[0u64..n]);
    ensures (0u64..n).all(|k| { defined(p[k]) and p[k] == 255u8 });
}

void fill_300(uint8* p, size_t n) {
    requires n <= 1024u64;
    owns uninitialized(p[0u64..n]);
    ensures (0u64..n).all(|k| { defined(p[k]) and p[k] == 44u8 });
}

void fill_any(uint8* p, int32 value, size_t n) {
    requires n <= 1024u64;
    owns uninitialized(p[0u64..n]);
    ensures (0u64..n).all(|k| { defined(p[k]) and p[k] == (value as uint8) });
}
```

```expect
pass
```
