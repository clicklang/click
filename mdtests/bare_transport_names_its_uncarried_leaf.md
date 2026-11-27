# A selected-premise proof refuses an overwritten quantified fact

The store to `dst[3]` changes a byte set by `memset`. The saved range fact cannot establish the current range after that write.

```c filename=fill.c
#include <string.h>

void fill(unsigned char *dst) { memset(dst, 7, 4); dst[3] = 0; }
```

```click
verifying "fill.c";

void fill(uint8* dst) {
    owns dst[0..4];
    ensures (0u64..4u64).all(|k| { defined(dst[k]) and dst[k] == 7 });
} by {
    step();
    mark filled;
    step();
    have (0u64..4u64).all(|k| { defined(dst[k]) and dst[k] == 7 }) by {
        close() using {
            at(filled, (0u64..4u64).all(|k| { defined(dst[k]) and dst[k] == 7 }));
        };
    }
}
```

```expect
fail: `close() using` could not prove the current goal from only its listed premises
```
