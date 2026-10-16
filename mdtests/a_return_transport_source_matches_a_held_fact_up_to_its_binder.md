# A return transport's source matches a held fact up to its binder's name

At a completed return outcome, `transport(source, target) using { }` may name
a held result-path fact as its source without listing it. The fact here is
`memset`'s postcondition, held with the binder its lowering chose, so the
written source names the same quantified fact with another binder. It is
accepted as a listed premise would be: up to the binder's name.

```c filename=ms.c
#include <string.h>

void fill_t(unsigned char *dst) { memset(dst, 7, 4); dst[4] = 0; }
```

```click
verifying "ms.c";

void fill_t(uint8* dst) {
    owns dst[0..5];
    ensures (0u64..4u64).all(|k| { defined(dst[k]) and dst[k] == 7 });
} by {
    execute();
    transport(at(statement(1).entry, (0u64..4u64).all(|k| { defined(dst[k]) and dst[k] == 7 })),
              (0u64..4u64).all(|k| { defined(dst[k]) and dst[k] == 7 })) using { }
}
```

```expect
pass
```
