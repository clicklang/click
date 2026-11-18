# Typed bit-field assignment does not guarantee a copy of padding

```c filename=fields.c
struct flags { unsigned int ready : 1; unsigned int busy : 1; };

int answer(void) {
    struct flags f;
    unsigned char *source = (unsigned char *)&f;
    source[0] = 3;
    struct flags copy = f;
    unsigned char *destination = (unsigned char *)&copy;
    return destination[0];
}
```

```click
verifying "fields.c";
int32 answer() { ensures result == result; }
```

```expect
fail:read of uninitialized storage
```
