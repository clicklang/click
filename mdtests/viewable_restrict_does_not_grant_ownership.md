# Restricting a viewability fact does not grant a resource

```c filename=copy.c
#include <string.h>
void copy4(unsigned char *dst, const unsigned char *src) { memcpy(dst, src, 4); }
```

```click
import click::separation;
verifying "copy.c";
void copy4(uint8* dst, const uint8* src) {
    requires viewable(memory(src[0..8]));
    owns dst[0..4];
    requires separate(memory(dst[0..4]), memory(src[0..4]));
} by {
    have contains(memory(src[0..8]), memory(src[0..4])) by {
        apply(separation::subrange(src, 0, 8, 0, 4)) using {};
    }
    have viewable(memory(src[0..4])) by {
        apply(separation::viewable_restrict(memory(src[0..8]), memory(src[0..4]))) using {
            viewable(memory(src[0..8]));
            contains(memory(src[0..8]), memory(src[0..4]));
        };
    }
    step();
}
```

```expect
fail: the required loan backing or binding is missing refused during planning
```
