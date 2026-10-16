# An overlapping store does not preserve initialized values

The store changes a byte admitted by the quantified guard.

```c filename=fill.c
#include <string.h>
void fill_t(unsigned char *dst) { memset(dst, 7, 4); dst[3] = 0; }
```

```click
import click::bytes;
verifying "fill.c";
void fill_t(uint8* dst) {
    owns dst[0..5];
    ensures (0u64..4u64).all(|k| { defined(dst[k]) and dst[k] == 7 });
    ensures bytes::all_equal(dst, 0u64, 4u64, 7u8);
} by { execute(); simp(); }
```

```expect
fail: checked outcome
```
