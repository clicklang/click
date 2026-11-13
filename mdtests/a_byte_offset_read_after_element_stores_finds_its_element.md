# a byte offset read after element stores finds its element

`q[i]` and `q[j]` are stored as elements; the read goes through
`b + 4 * i`, the bytes of `q` at the written byte offset `4 * i`. Resolving the
read places it against each store: the bytes `4 * i` are element `i` where the
`int32` product does not wrap, which the bounds on `i` decide, so the read is
the store to `q[i]` and is apart from the store to `q[j]` because `i != j`.
The read happens in the statement that forms the byte offset, before that
statement's facts reach the equality graph, so memory resolution reads the
product as an element index itself, asking the one overflow question.

```c filename=a_byte_offset_read_after_element_stores_finds_its_element.c
#include <stdint.h>

int32_t frame(int32_t* q, int i, int j, int32_t v, int32_t w) {
    char* b;
    b = (char*)(void*) q;
    q[i] = v;
    q[j] = w;
    return *(int32_t*)(void*)(b + 4 * i);
}
```

```click
verifying "a_byte_offset_read_after_element_stores_finds_its_element.c";

int32_t frame(int32_t* q, int i, int j, int32_t v, int32_t w) {
    requires i >= 0;
    requires i < 4;
    requires j >= 0;
    requires j < 4;
    requires i != j;
    owns q[0..4];
    ensures result == v;
}
```

```expect
pass
```
