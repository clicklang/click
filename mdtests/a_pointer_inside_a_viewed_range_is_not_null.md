# A pointer inside a viewed range is not null

`b->content` points to a viewed buffer of `b->length` bytes and
`b->offset` lies inside it, so `b->content + b->offset` points into a live
object and is not null (C11 6.3.2.3p3). Without that law the `NULL` test
left the infeasible `return 0` path open, and the true claim `result == 1`
was refused there. `separation::viewable_offset_nonnull` states it from the
explicit view and bounds. It needs no `content != 0` requirement: the view of
a nonempty range already says the base is an object.

```c filename=a_pointer_inside_a_viewed_range_is_not_null.c
#include <stddef.h>

typedef struct {
    const unsigned char *content;
    size_t length;
    size_t offset;
} parse_buffer;

int at_valid_position(parse_buffer * const b) {
    const unsigned char *p = b->content + b->offset;
    if (p != NULL) {
        return 1;
    }
    return 0;
}
```

```click
verifying "a_pointer_inside_a_viewed_range_is_not_null.c";
import click::separation;

int32 at_valid_position(parse_buffer * const b) {
    views b->content;
    views b->length;
    views b->offset;
    requires b->offset < b->length;
    views b->content[0..b->length];
    ensures result == 1;
} by {
    have 0u64 < b->length by { solve(); }
    have b->offset <= b->length by { solve(); }
    apply(separation::viewable_offset_nonnull(b->content, 0u64, b->length, b->offset));
}
```

```expect
pass
```
