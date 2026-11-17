# A later-word bit-field keeps its signed value and neighboring members

```c filename=fields.c
struct fields {
    unsigned int prefix : 28;
    signed int delta : 9;
    unsigned int tail : 23;
    unsigned int end : 32;
};

int answer(void) {
    struct fields f = { .end = 0x80000000u, .delta = -2, .prefix = 3 };
    struct fields *p = &f;
    p->delta++;
    struct fields copy = f;
    p->delta = 0;
    const unsigned char *bytes = (const unsigned char *)&copy;
    return sizeof(struct fields) == 12 && sizeof(f) == 12 &&
           copy.prefix == 3 && copy.delta == -1 && copy.tail == 0 &&
           bytes[4] == 255 && bytes[5] == 1 && f.delta == 0 &&
           copy.end > 0 && bytes[11] == 128;
}
```

```click
verifying "fields.c";
int32 answer() { ensures result == 1; }
```

```expect
pass
```
