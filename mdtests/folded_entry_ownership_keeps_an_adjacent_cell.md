# Folded entry ownership keeps an adjacent cell

Entry admission retains the instance and the separate adjacent owner. Later
observation and completion use that established partition.

```c filename=folded_entry_ownership_keeps_an_adjacent_cell.c
#include <stdint.h>
void keep(int32_t *p) {}
```

```click
resource cell(p: int32_t*) {
    field tag: int32;
    owns p[0..1];
}

verifying "folded_entry_ownership_keeps_an_adjacent_cell.c";

void keep(int32_t *p) {
    owns r: cell(p);
    owns p[1..2];
}
```

```expect
pass
```
