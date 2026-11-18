# Struct assignment through a writable pointer from a const view

```c filename=fields.c
struct fields { unsigned int count : 3; signed int delta : 4; };

int answer(void) {
    struct fields source = { .count = 5, .delta = -2 };
    struct fields dest = {0};
    const struct fields *read = &source;
    struct fields *write = &dest;
    *write = *read;
    source.count = 0;
    write->delta += 1;
    return dest.count + dest.delta;
}
```

```click
verifying "fields.c";
int32 answer() { ensures result == 4; }
```

```expect
pass
```
