# Named transport carries guarded definedness

The terminator store leaves the initialized prefix and its values unchanged.

```c filename=fill.c
#include <string.h>
void fill_t(unsigned char *dst) { memset(dst, 7, 4); dst[4] = 0; }
```

```click
import click::bytes;
verifying "fill.c";
void fill_t(uint8* dst) {
    owns dst[0..5];
    ensures (0u64..4u64).all(|k| { defined(dst[k]) and dst[k] == 7 });
    ensures bytes::all_equal(dst, 0u64, 4u64, 7u8);
} by {
    step();
    mark filled;
    step();
    transport(
        at(filled, (0u64..4u64).all(|k| { defined(dst[k]) and dst[k] == 7 })),
        (0u64..4u64).all(|k| { defined(dst[k]) and dst[k] == 7 })
    );
    execute();
    simp();
}
```

```expect
pass
```
