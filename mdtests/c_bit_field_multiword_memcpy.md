# A later-word field survives a representation copy through a character array

```c filename=fields.c
#include <string.h>

struct fields { unsigned int prefix : 31, value : 10, other : 12; };

int answer(void) {
    struct fields source;
    struct fields target;
    unsigned char image[sizeof(source)];
    source.value = 257;
    memcpy(image, &source, sizeof(source));
    memcpy(&target, image, sizeof(target));
    unsigned char *bytes = (unsigned char *)&target;
    bytes[5] = 2;
    return target.value == 513 && bytes[4] == 1;
}
```

```click
verifying "fields.c";
int32 answer() { ensures result == 1; }
```

```expect
pass
```
