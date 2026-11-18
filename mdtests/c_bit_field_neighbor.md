# A bit-field store preserves its neighbor

```c filename=flags.c
struct flags {
    unsigned int ready : 1;
    unsigned int busy : 1;
};

int answer(void) {
    struct flags f = { .ready = 0, .busy = 1 };
    f.ready = 1;
    return f.ready && f.busy;
}
```

```click
verifying "flags.c";
int32 answer() { ensures result == 1; }
```

```expect
pass
```
