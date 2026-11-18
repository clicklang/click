# Contradictory folded entry ownership is refused before execution

The entry clause list describes one cell twice, inside the instance and beside
it. Reject the raw description even when the proof never unfolds the instance.

```c filename=contradictory_folded_entry_ownership_is_refused_before_execution.c
#include <stdint.h>
void keep(int32_t *p) {}
```

```click
resource cell(p: int32_t*) {
    field tag: int32;
    owns p[0..1];
}

verifying "contradictory_folded_entry_ownership_is_refused_before_execution.c";

void keep(int32_t *p) {
    owns r: cell(p);
    owns p[0..1];
}
```

```expect
fail: overlapping owned memory resource facts
```
