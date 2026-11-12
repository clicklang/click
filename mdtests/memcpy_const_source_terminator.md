# Const-source copy preserves ownership for the terminator

```c filename=memcpy_const_source_terminator.c
#include <string.h>
void copy_prefix(char *dst, const char *src, unsigned long n) {
    memcpy(dst, src, n);
    dst[n] = '\0';
}
```

```click
verifying "memcpy_const_source_terminator.c";
void copy_prefix(char* dst, const char* src, uint64 n) {
    requires n < 32u64;
    views src[0u64..n];
    owns dst[0u64..32u64];
    requires separate(memory(dst[0u64..32u64]), memory(src[0u64..n]));
    ensures dst[n] == '\0';
} by {
    step();
    have 0u64 <= n by { solve(); }
    have contains(memory(dst[0u64..32u64]), memory(dst[n])) by {
        apply(click::separation::contains_element(dst, 0u64, 32u64, n)) using { 0u64 <= n; n < 32u64; };
    }
    have contains(memory(src[0u64..n]), memory(src[0u64..n])) by {
        apply(click::separation::contains_refl(memory(src[0u64..n])));
    }
    have separate(memory(dst[n]), memory(src[0u64..n])) by {
        apply(click::separation::restrict(memory(dst[0u64..32u64]), memory(src[0u64..n]), memory(dst[n]), memory(src[0u64..n]))) using {
            separate(memory(dst[0u64..32u64]), memory(src[0u64..n]));
            contains(memory(dst[0u64..32u64]), memory(dst[n]));
            contains(memory(src[0u64..n]), memory(src[0u64..n]));
        };
    }
}
```

```expect
pass
```
