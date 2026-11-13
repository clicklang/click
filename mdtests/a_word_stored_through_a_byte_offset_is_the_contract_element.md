# a word stored through a byte offset is the contract's element

The store writes `v` through `b + i * 4`, the bytes of `q` at the written byte
offset `i * 4`; the contract reads `q[i]`. The two addresses are spelled
differently and are one address because `i * 4` does not wrap, which the
pointer arithmetic records as `defined(i * 4)`. The equality graph joins the
byte offset to element `i` at stride four, so `assumption()` finds the stored
value for `q[i]` in the outcome state.

The implicit closer does not try that `have` for an `ensures` whose read is
spelled differently from its store, so the proof names it. Before the byte
offset kept its spelling, lowering rewrote the store's address into `q + i`
and the contract read resolved to the stored value by its spelling.

```c filename=a_word_stored_through_a_byte_offset_is_the_contract_element.c
#include <stdint.h>

void set(int32_t* q, int i, int32_t v) {
    char* b;
    b = (char*)(void*) q;
    *(int32_t*)(void*)(b + i * 4) = v;
}
```

```click
verifying "a_word_stored_through_a_byte_offset_is_the_contract_element.c";

void set(int32_t* q, int i, int32_t v) {
    requires i >= 0;
    requires i < 4;
    owns q[0..4];
    ensures q[i] == v;
} by {
    step();
    step();
    step();
    step();
    have q[i] == v by {
        assumption();
    }
    assumption();
    assumption();
}
```

```expect
pass
```
