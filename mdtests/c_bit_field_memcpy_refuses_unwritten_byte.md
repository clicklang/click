# A partial representation copy clears destination byte readability

```c filename=fields.c
#include <string.h>

struct flags { unsigned int ready : 1; unsigned int busy : 1; };

int answer(void) {
    struct flags source;
    unsigned char image[sizeof(struct flags)] = { 3 };
    source.ready = 1;
    memcpy(image, &source, sizeof(source));
    return image[0];
}
```

```click
verifying "fields.c";
int32 answer() { ensures result == result; }
```

```expect
fail:read of uninitialized storage
```
