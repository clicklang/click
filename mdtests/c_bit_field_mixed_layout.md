# Ordinary fields can share a record with allocation-word bit-fields

```c filename=fields.c
#include <string.h>

struct header {
    unsigned char kind;
    unsigned int length : 17;
    unsigned int flags : 9;
    unsigned char checksum;
};

int answer(void) {
    struct header h = { .kind = 9, .length = 1, .flags = 3 };
    unsigned char *checksum = &h.checksum;
    *checksum = 7;
    struct header *p = &h;
    p->length++;
    unsigned char *bytes = (unsigned char *)&h;
    bytes[1] = 19;
    struct header copy = h;
    struct header output;
    memcpy(&output, &copy, sizeof(copy));
    return sizeof(h) == 8 && sizeof(h.kind) == 1 && __builtin_offsetof(struct header, checksum) == 6 &&
           output.kind == 9 && output.length == 19 &&
           output.flags == 3 && output.checksum == 7;
}
```

```click
verifying "fields.c";
int32 answer() { ensures result == 1; }
```

```expect
pass
```
