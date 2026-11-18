# A nonunit folded entry body cannot duplicate owned memory

An explicit quantity and two repeated clauses describe the same two demands.
Following the body's written memory once must not erase its multiplicity.

```c filename=a_nonunit_folded_entry_body_cannot_duplicate_owned_memory.c
#include <stdint.h>
void keep(int32_t *p) {}
```

```click
resource cell(p: int32_t*) {
    owns p[0..1];
}

verifying "a_nonunit_folded_entry_body_cannot_duplicate_owned_memory.c";

void keep(int32_t *p) {
    owns 2 of cell(p);
}
```

```expect
fail: overlapping owned memory resource facts
```
