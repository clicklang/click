# A heap struct read through another struct is refused

A member store gives an allocated cell the type of the struct it goes
through, so reading the cell through a struct of another type, though of the
same layout, is refused.

```c filename=heap.c
#include <stdlib.h>
struct a { int x; };
struct b { int y; };

int structs(void) {
    struct a *pa = malloc(sizeof(struct a));
    if (!pa) return 0;
    pa->x = 1;
    void *v = pa;
    struct b *pb = v;
    int r = pb->y;
    free(pa);
    return r;
}
```

```click
verifying "heap.c";

int32 structs() {
    ensures true;
} by {
    execute();
}
```

```expect
fail: an object of type `struct a` accessed through an lvalue of type `struct b`
```
