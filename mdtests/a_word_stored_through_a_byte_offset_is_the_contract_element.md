# a word stored through a byte offset is the contract's element

The store writes `v` through `b + i * 4`, and the contract reads `q[i]`.
The proof expresses both addresses as byte pointers, then rewrites the typed
load to the recorded store address. The bounds on `i` keep the byte offset in
range.

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
    step_until(statement(2).entry);
    step();
    have exact(*((program::b + i * 4) as (int32 *))) == v by close();
    have ((q + i) as (int8 *)) == (program::b + i * 4) by close();
    have load<int32>((q + i) as (int8 *)) == v by {
        rewrite((q + i) as (int8 *), program::b + i * 4);
        close();
    }
    have q[i] == v by close();
    step_until(function.exit);
    close();
}
```

```expect
pass
```
