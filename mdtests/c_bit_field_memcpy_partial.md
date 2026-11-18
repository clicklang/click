# memcpy preserves an initialized field in a partially initialized struct

```c filename=fields.c
#include <string.h>

struct flags {
    unsigned int ready : 1;
    unsigned int busy : 1;
};

int answer(void) {
    struct flags source;
    struct flags target;
    source.ready = 1;
    memcpy(&target, &source, sizeof(source));
    return target.ready;
}
```

```click
verifying "fields.c";
int32 answer() { ensures result == 1; }
```

```expect
pass
```
