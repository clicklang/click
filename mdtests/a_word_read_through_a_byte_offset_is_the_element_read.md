# a word read through a byte offset is the element read

`b + i * 4`, with `b` the bytes of `q`, keeps its written byte offset `i * 4`
when it is formed: lowering never reads the facts to choose an address
(`docs/internals/spellability.md`, "Lowering is fact-stable"). It is the
address of `q[i]` only where the `int32` product `i * 4` does not wrap. The C
multiplication refuses its wrapping path, and the pointer arithmetic records
that `i * 4` is defined, so the equality graph joins the byte offset to element
`i` at stride four. The two reads of the entry memory are then one read.

Before the byte offset kept its spelling, lowering rewrote it into the element
index whenever the facts ruled out the wrap, and the two reads were one term.
`a_byte_offset_product_that_may_wrap_is_refused.md` is the case the facts do
not rule out.

```c filename=a_word_read_through_a_byte_offset_is_the_element_read.c
#include <stdint.h>

int32_t get(int32_t* q, int i) {
    char* b;
    b = (char*)(void*) q;
    return *(int32_t*)(void*)(b + i * 4);
}
```

```click
verifying "a_word_read_through_a_byte_offset_is_the_element_read.c";

int32_t get(int32_t* q, int i) {
    requires i >= 0;
    requires i < 4;
    views q[0..4];
    ensures result == q[i];
}
```

```expect
pass
```
