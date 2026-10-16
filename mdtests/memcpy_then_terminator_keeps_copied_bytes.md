# Copied bytes survive the terminator store after `memcpy`

`label_copy`'s pattern: copy `n` bytes, then store the terminator at
`dst[n]`, then state the copied bytes. `memcpy` states
`bytes::equal(dst, 0u64, old(src), 0u64, n)`, a guarded universal over the
reads `dst[k]` and `src[k]` for `k < n`. The `transport` carries it past the
terminator store with the checked quantified frame, which takes the `uint64`
binder like any C integer binder and assumes its guard `k < n` for each
read: `dst[k]` misses the store at `dst[n]` by that guard, and `src[k]` is
kept apart from `dst` by the `separate` requirement. The written source names
its own binder; `transport` accepts it as the call's postcondition, which
holds the binder its lowering chose. The `char *` arguments read the same
`uint8` bytes in the `have`, the call's fact and the unfolded postcondition.

```c filename=copy.c
#include <string.h>
void copy_n(char *dst, const char *src, unsigned long n) { memcpy(dst, src, n); dst[n] = '\0'; }
```

```click
import click::bytes;
verifying "copy.c";
void copy_n(char* dst, const char* src, uint64 n) {
    views src[0u64..n];
    owns dst[0u64..n + 1u64];
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
        );
    }
    execute();
}
```

```expect
pass
```
