# A neighboring bit-field stays uninitialized

```c filename=flags.c
struct flags {
    unsigned int ready : 1;
    unsigned int busy : 1;
};

int answer(void) {
    struct flags f;
    f.ready = 1;
    return f.busy;
}
```

```click
verifying "flags.c";
int32 answer() { ensures result == 0; }
```

```expect
fail:read of uninitialized storage
```
