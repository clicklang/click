# Struct assignment replaces initialization of the destination fields

```c filename=fields.c
struct flags { unsigned int ready : 1; unsigned int busy : 1; };

int answer(void) {
    struct flags source;
    struct flags dest = {1, 1};
    source.ready = 1;
    dest = source;
    return dest.busy;
}
```

```click
verifying "fields.c";
int32 answer() { ensures result == result; }
```

```expect
fail:read of uninitialized storage
```
