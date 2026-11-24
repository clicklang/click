# A pointer subtraction across a preserved field read verifies

After the store into `out`, `b->content` is read again. The proof shows it
equals the read `end` was formed from, so both pointers are in one object.
The subtraction's operands are still different terms. It was refused as
unsupported offsets; it now has the signed difference of their addresses as
its value, the same term whatever the facts say, for the proof to relate.

```c filename=a_pointer_subtraction_across_a_preserved_field_read_verifies.c
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
verifying "a_pointer_subtraction_across_a_preserved_field_read_verifies.c";

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
} by {
    step_until(statement(2).entry);
    step();
    have separate(memory(out[0..1]), memory(b->content)) by { close(); }
    have separate(statement(2).footprint, memory(b->content)) by { close(); }
    have b->content == at(statement(2).entry, b->content) by {
        preserve(memory(b->content), statement(2));
    }
    step();
}
```

```expect
pass
```
