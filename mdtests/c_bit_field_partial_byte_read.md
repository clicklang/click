# A field store does not initialize a whole byte

```c filename=fields.c
struct flags { unsigned int ready : 1; unsigned int busy : 1; };

int answer(void) {
    struct flags f;
    unsigned char *bytes = (unsigned char *)&f;
    f.ready = 1;
    return bytes[0];
}
```

```click
verifying "fields.c";
int32 answer() { ensures result == result; }
```

```expect
fail:read of uninitialized storage
```
