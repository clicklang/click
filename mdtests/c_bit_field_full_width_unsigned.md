# A full-width unsigned bit-field retains its unsigned type

```c filename=fields.c
struct counter { unsigned int value : 32; };

int answer(void) {
    struct counter c = {4294967295u};
    return c.value > 0;
}
```

```click
verifying "fields.c";
int32 answer() { ensures result == 1; }
```

```expect
pass
```
