# Two folded entry instances cannot own the same cell

Distinct instance identities do not supply two units of their shared memory.
Reject the raw entry section without requiring either instance to be unfolded.

```c filename=two_folded_entry_instances_cannot_own_the_same_cell.c
#include <stdint.h>
void keep(int32_t *p) {}
```

```click
resource cell(p: int32_t*) {
    field tag: int32;
    owns p[0..1];
}

verifying "two_folded_entry_instances_cannot_own_the_same_cell.c";

void keep(int32_t *p) {
    owns first: cell(p);
    owns second: cell(p);
}
```

```expect
fail: overlapping owned memory resource facts
```
