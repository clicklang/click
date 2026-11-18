# Repeated folded entry clauses cannot share one cell

The section's normalized context can combine identical heads into a quantity.
Raw body admission must still see both original written clauses.

```c filename=repeated_folded_entry_clauses_cannot_share_one_cell.c
#include <stdint.h>
void keep(int32_t *p) {}
```

```click
resource cell(p: int32_t*) {
    owns p[0..1];
}

verifying "repeated_folded_entry_clauses_cannot_share_one_cell.c";

void keep(int32_t *p) {
    owns cell(p);
    owns cell(p);
}
```

```expect
fail: overlapping owned memory resource facts
```
