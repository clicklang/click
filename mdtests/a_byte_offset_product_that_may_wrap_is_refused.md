# a byte offset product that may wrap is refused

With no upper bound on `i`, `i * 4` may overflow `int`. The byte offset
`b + i * 4` and the element `q[i]` are then not one address: the element
offset sign-extends `i` before scaling, the byte offset sign-extends the
wrapped product. C makes the overflow undefined, so the read is refused at the
multiplication, and no path relates the two spellings without the fact that
`i * 4` is defined. `a_word_read_through_a_byte_offset_is_the_element_read.md`
is the same read with the bound.

```c filename=a_byte_offset_product_that_may_wrap_is_refused.c
#include <stdint.h>

int32_t get(int32_t* q, int i) {
    char* b;
    b = (char*)(void*) q;
    return *(int32_t*)(void*)(b + i * 4);
}
```

```click
verifying "a_byte_offset_product_that_may_wrap_is_refused.c";

int32_t get(int32_t* q, int i) {
    requires i >= 0;
    views q[0..4];
    ensures result == q[i];
}
```

```expect
fail: `step()` produced undefined behavior: signed overflow
```
