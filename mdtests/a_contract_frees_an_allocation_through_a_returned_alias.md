# A contract frees an allocation named through a returned alias

`identity` returns the pointer it was given, `ensures result == p`, so `q`
names `p`'s allocation. `release(q)` consumes that allocation: the call
retires the storage the allocation's creation is recorded under, not the
block `q` happens to be spelled by.

```c filename=alias_release.c
#include <stdlib.h>
int32* identity(int32* p) { return p; }
void release(int32* p);
void dispose(void) {
    int32* p = malloc(4);
    if (p == 0) return;
    int32* q = identity(p);
    release(q);
}
```

```click
verifying "alias_release.c";
int32* identity(int32* p) { ensures result == p; }
extern void release(int32* p) { consumes allocation(p, 4); consumes uninitialized(*p); }
void dispose() { ensures true; }
```

```expect
pass
```
