# Copied `unsigned char` bytes survive the terminator store

The reduction of `label_copy` over `unsigned char` buffers with a constant
count: `memcpy(dst, src, 4); dst[4] = 0;` and then the copied bytes. The
`src[k]` reads under the postcondition's guard `k < 4u64` are an unsigned
64-bit index into the 32-bit-bounded range `src[0..4]` of the `separate`
requirement, so typed range membership places them by the exact guard fact
before the separation keeps them apart from the store at `dst[4]`. Both the
explicit `transport` and the smart `execute(); simp();` close it.

```c filename=copy.c
#include <string.h>
void copy_u(unsigned char *dst, const unsigned char *src) { memcpy(dst, src, 4); dst[4] = 0; }
void copy_u_smart(unsigned char *dst, const unsigned char *src) { memcpy(dst, src, 4); dst[4] = 0; }
```

```click
import click::bytes;
verifying "copy.c";
void copy_u(uint8* dst, const uint8* src) {
    views src[0..4];
    owns dst[0..5];
    requires separate(memory(dst[0..5]), memory(src[0..4]));
    ensures bytes::equal(dst, 0u64, src, 0u64, 4u64);
} by {
    unfold(bytes::equal);
    step();
    mark copied;
    step();
    have bytes::equal(dst, 0u64, src, 0u64, 4u64) by {
        transport(
            at(copied, (0u64..4u64).all(|k| { dst[0u64 + k] == old(src[0u64 + k]) })),
            (0u64..4u64).all(|k| { dst[0u64 + k] == src[0u64 + k] })
        );
    }
    execute();
}
void copy_u_smart(uint8* dst, const uint8* src) {
    views src[0..4];
    owns dst[0..5];
    requires separate(memory(dst[0..5]), memory(src[0..4]));
    ensures bytes::equal(dst, 0u64, src, 0u64, 4u64);
} by { execute(); simp(); }
```

```expect
pass
```
