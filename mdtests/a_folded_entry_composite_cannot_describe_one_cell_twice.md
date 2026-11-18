# A folded entry composite cannot describe one cell twice

Raw entry elaboration retains both written demands. A declaration is not a
held-body receipt and cannot make duplicate memory clauses disappear by merging.

```c filename=a_folded_entry_composite_cannot_describe_one_cell_twice.c
#include <stdint.h>
void keep(int32_t *p) {}
```

```click
resource twice(p: int32_t*) {
    owns p[0..1];
    owns p[0..1];
}

verifying "a_folded_entry_composite_cannot_describe_one_cell_twice.c";

void keep(int32_t *p) {
    owns twice(p);
}
```

```expect
fail: overlapping owned memory resource facts
```
