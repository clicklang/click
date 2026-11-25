# A bare `transport` refuses an overwritten quantified fact

The store to `dst[3]` changes a byte set by `memset`. Bare transport
reports the historical source and the current target when it cannot construct
a proof of the full range.

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
    transport(at(filled, (0u64..4u64).all(|k| { defined(dst[k]) and dst[k] == 7 })),
              (0u64..4u64).all(|k| { defined(dst[k]) and dst[k] == 7 }));
}
```

```expect
fail: `transport` found no checked proof from its source
```
