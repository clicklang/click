# An unnamed bit-field does not initialize its bits

```c filename=fields.c
struct fields { unsigned char kind; unsigned int : 3, flags : 5; };

int answer(void) {
    struct fields f = { 1, 2 };
    struct fields copy = f;
    const unsigned char *bytes = (const unsigned char *)&copy;
    return bytes[1];
}
```

```click
verifying "fields.c";
int32 answer() { ensures result == result; }
```

```expect
fail:read of uninitialized storage
```
