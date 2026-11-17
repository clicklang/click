# A returned allocation still requires cleanup

Returning the cleanup anchor to the caller does not discharge it. The caller
must free the allocation or export it through its own contract.

```c filename=pass_through.c
#include <stdlib.h>
int *pass(int *p) { return p; }
int caller(void) {
    int *p = malloc(4);
    if (p == 0) return 0;
    int *q = pass(p);
    return 1;
}
```

```click
verifying "pass_through.c";
int32* pass(int32* p) {
    consumes allocation(p, 4);
    consumes uninitialized(p[0..1]);
    ensures result == p;
    produces allocation(result, 4);
    produces uninitialized(result[0..1]);
}
int32 caller() { ensures result == 0 or result == 1; }
```

```expect
fail: live allocation obligation was neither returned nor freed
```
