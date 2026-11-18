# A partial bit-field survives a copy through a character array

```c filename=fields.c
#include <string.h>

struct flags { unsigned int ready : 1; unsigned int busy : 1; };

int answer(void) {
    struct flags source;
    struct flags target;
    unsigned char image[sizeof(struct flags)];
    source.ready = 1;
    memcpy(image, &source, sizeof(source));
    memcpy(&target, image, sizeof(target));
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
