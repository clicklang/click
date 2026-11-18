# Nonunit folded entry bodies keep empty and readonly footprints

Quantities remain available for bodies with no exclusive bytes. Empty owned
ranges and shared read authority do not duplicate a nonempty owner.

```c filename=nonunit_folded_entry_bodies_keep_empty_and_readonly_footprints.c
#include <stdint.h>
void keep_empty(int32_t *p) {}
void keep_readonly(int32_t *p) {}
```

```click
resource empty(p: int32_t*) {
    owns p[0..0];
}

resource readonly(p: int32_t*) {
    views p[0..1];
}

verifying "nonunit_folded_entry_bodies_keep_empty_and_readonly_footprints.c";

void keep_empty(int32_t *p) {
    owns 2 of empty(p);
}

void keep_readonly(int32_t *p) {
    owns 2 of readonly(p);
}
```

```expect
pass
```
