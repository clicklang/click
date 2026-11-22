# a word stored through a byte offset is the contract's element

The store writes `v` through `b + i * 4`, and the contract reads `q[i]`.
The proof cites the value of the read at the point that performed the write
and proves that both expressions address the same bytes. The checked bounds
on `i` ensure that `i * 4` does not wrap.

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
    have at(statement(2).exit, exact(*((program::b + i * 4) as (int32 *))) == v) by {
        known();
    }
    have at(statement(2).exit, address(q + i) == address(((program::b + i * 4) as (int32 *)))) by {
        solve();
    }
    have q[i] == v by {
        solve() using {
            at(statement(2).exit, exact(*((program::b + i * 4) as (int32 *))) == v);
            at(statement(2).exit, address(q + i) == address(((program::b + i * 4) as (int32 *))));
        };
    }
    known();
    known();
}
```

```expect
pass
```
