# Byte and bit-field operations observe the same memory

```c filename=fields.c
struct flags {
    unsigned int ready : 1;
    unsigned int busy : 1;
};

int answer(void) {
    struct flags f = { .ready = 1, .busy = 0 };
    unsigned char *bytes = (unsigned char *)&f;
    bytes[0] = 2;
    int busy = f.busy;
    f.ready = 1;
    return busy && bytes[0] == 3;
}
```

```click
verifying "fields.c";
int32 answer() { ensures result == 1; }
```

```expect
pass
```
