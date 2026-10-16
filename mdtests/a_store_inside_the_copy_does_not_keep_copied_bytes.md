# A store inside the copied range does not keep the copied bytes

The refusal beside `memcpy_then_terminator_keeps_copied_bytes.md`: the
terminator is stored at `dst[n - 1]`, which the guard `k < n` does not keep
apart from the read `dst[n - 1]`. The quantified frame finds no evidence for
that read, so the copied-bytes fact is not carried past the store, with the
frame evidence listed explicitly.

```c filename=copy.c
#include <string.h>
void copy_n(char *dst, const char *src, unsigned long n) { memcpy(dst, src, n); dst[n - 1] = '\0'; }
```

```click
import click::bytes;
verifying "copy.c";
void copy_n(char* dst, const char* src, uint64 n) {
    views src[0u64..n];
    owns dst[0u64..n + 1u64];
    requires 1u64 <= n;
    requires n < 32u64;
    requires separate(memory(dst[0u64..n + 1u64]), memory(src[0u64..n]));
    ensures bytes::equal(dst, 0u64, src, 0u64, n);
} by {
    unfold(bytes::equal);
    step();
    mark copied;
    step();
    have bytes::equal(dst, 0u64, src, 0u64, n) by {
        transport(
            at(copied, (0u64..n).all(|k| {
                ((uint8*)dst)[0u64 + k] == old(((uint8*)src)[0u64 + k])
            })),
            (0u64..n).all(|k| { ((uint8*)dst)[0u64 + k] == ((uint8*)src)[0u64 + k] })
        ) using {
            at(copied, (0u64..n).all(|k| {
                ((uint8*)dst)[0u64 + k] == old(((uint8*)src)[0u64 + k])
            }));
            separate(memory(dst[0u64..n + 1u64]), memory(src[0u64..n]));
        };
    }
    execute();
}
```

```expect
fail: `transport using` found no frame evidence carrying its source fact to the target's state
```
