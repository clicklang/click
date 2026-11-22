# An empty viewed range does not make its base nonnull

C allows a null pointer with a zero length, so a view of `p[0..n]` says
nothing about `p` when `n` may be zero. `separation::viewable_offset_nonnull`
requires a nonempty range, and without `0 < n` its application is refused.

```c filename=an_empty_viewed_range_does_not_make_its_base_nonnull.c
#include <stddef.h>

int has_buffer(const unsigned char *p, size_t n) {
    if (p != NULL) {
        return 1;
    }
    return 0;
}
```

```click
verifying "an_empty_viewed_range_does_not_make_its_base_nonnull.c";
import click::separation;

int32 has_buffer(const uint8* p, uint64 n) {
    views p[0..n];
    ensures result == 1;
} by {
    apply(separation::viewable_offset_nonnull(p, 0u64, n, 0u64));
}
```

```expect
fail: goal: 0u64 < n
```
