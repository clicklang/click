# A bit-field store can initialize part of a fresh byte

```c filename=flags.c
struct flags {
    unsigned int ready : 1;
    unsigned int busy : 1;
};

int answer(void) {
    struct flags f;
    f.ready = 1;
    int first = f.ready;
    f.busy = 1;
    return first + f.ready + f.busy;
}
```

```click
verifying "flags.c";
int32 answer() { ensures result == 3; }
```

```expect
pass
```
