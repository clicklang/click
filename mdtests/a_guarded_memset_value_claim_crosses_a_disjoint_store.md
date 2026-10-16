# A `memset` value claim crosses a disjoint store

`bytes::all_equal(dst, 0u64, 4u64, 7u8)` unfolds to the values alone,
`(0u64..4u64).all(|k| { dst[k] == 7u8 })`. After `dst[4] = 0` the only
fact naming those cells is `memset`'s guarded postcondition at the call's
exit, which also carries `defined(dst[k])`. `simp` selects it by its indexed
conjunct projection and transports it to the goal in one checked step: the
quantified frame shows the store separate from each read under `k < 4` and
drops the `defined(..)` conjunct by conjunction elimination.

```c filename=fill.c
#include <string.h>

void fill(unsigned char *dst) {
    memset(dst, 7, 4);
    dst[4] = 0;
}
```

```click
import click::bytes;
verifying "fill.c";

void fill(uint8* dst) {
    owns dst[0..5];
    ensures bytes::all_equal(dst, 0u64, 4u64, 7u8);
} by {
    execute();
    simp();
}
```

```expect
pass
```
