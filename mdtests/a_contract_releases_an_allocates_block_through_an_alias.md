# A contract releases an allocation a contract made, through an alias

`make`'s block is new, `allocates(result, 4)`, and `identity` returns the
pointer it was given, `ensures result == p`. `release(q)` consumes
`allocation(q, 4)`: the caller holds that token under `p`, and finds it
through `q == p` as the owned token, not among the views it supplies.

```c filename=alias_release.c
#include <stdlib.h>
int32* identity(int32* p) { return p; }
int32* make(void);
void release(int32* p);
void dispose(void) {
    int32* p = make();
    int32* q = identity(p);
    release(q);
}
```

```click
verifying "alias_release.c";
int32* identity(int32* p) { ensures result == p; }
extern int32* make() { allocates(result, 4); produces *result; ensures result != 0; }
extern void release(int32* p) { consumes allocation(p, 4); consumes uninitialized(*p); }
void dispose() { ensures true; }
```

```expect
pass
```
