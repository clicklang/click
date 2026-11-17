# Named bit-field updates and C integer promotions

```c filename=fields.c
struct fields {
    unsigned int count : 3;
    signed int delta : 4;
};

int answer(void) {
    struct fields f = { .count = 3, .delta = -4 };
    struct fields *p = &f;
    p->count++;
    struct fields copy = f;
    p->delta = 2;
    return (copy.count + copy.delta == 0) && (copy.count - 5 < 0);
}
```

```click
verifying "fields.c";
int32 answer() { ensures result == 1; }
```

```expect
pass
```
