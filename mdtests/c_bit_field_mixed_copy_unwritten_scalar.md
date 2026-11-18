# Mixed-record assignment replaces the initialization of ordinary members

```c filename=fields.c
struct fields { unsigned int flags : 5; unsigned int count; };

unsigned int answer(void) {
    struct fields source;
    source.flags = 1;
    struct fields target = { 0, 44 };
    target = source;
    return target.count;
}
```

```click
verifying "fields.c";
uint32 answer() { ensures result == result; }
```

```expect
fail:read of uninitialized storage
```
