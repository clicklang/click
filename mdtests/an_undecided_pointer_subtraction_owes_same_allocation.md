# An undecided pointer subtraction owes `same_allocation`

C defines `end - b->content` only for two pointers into one array object
(C11 6.5.6p9). After the store into `out`, `b->content` is a new read the
proof has not related to the one `end` was formed from, so the step cannot
decide it. That was reported as undefined behavior the step produced, with no
goal. The precondition is an obligation at the subtraction, stated as
`same_allocation`, which the proof may establish.

```c filename=an_undecided_pointer_subtraction_owes_same_allocation.c
#include <stddef.h>

typedef struct {
    const unsigned char *content;
    size_t length;
    size_t offset;
} parse_buffer;

unsigned char *get_buffer(void);

size_t consumed(parse_buffer * const b) {
    const unsigned char *end = b->content + b->offset;
    unsigned char *out = get_buffer();
    *out = 0;
    return (size_t)(end - b->content);
}
```

```click
verifying "an_undecided_pointer_subtraction_owes_same_allocation.c";

extern uint8* get_buffer() {
    ensures result != 0;
    produces result[0..1];
}

uint64 consumed(parse_buffer * const b) {
    views b->content;
    views b->length;
    views b->offset;
    requires b->offset < b->length;
    views b->content[0..b->length];
    ensures true;
}
```

```expect
fail: `step()` requires an explicit prerequisite proof (pointer subtraction requires both pointers in one object (C11 6.5.6p9))
```
