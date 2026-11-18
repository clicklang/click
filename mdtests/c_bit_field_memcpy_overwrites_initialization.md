# Copying an unwritten field clears the previous initialization of the destination

```c filename=fields.c
#include <string.h>

struct flags { unsigned int ready : 1; unsigned int busy : 1; };

int answer(void) {
    struct flags source;
    struct flags target;
    unsigned char *bytes = (unsigned char *)&target;
    bytes[0] = 3;
    source.ready = 1;
    memcpy(&target, &source, sizeof(source));
    return target.busy;
}
```

```click
verifying "fields.c";
int32 answer() { ensures result == result; }
```

```expect
fail:read of uninitialized storage
```
