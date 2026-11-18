# An unbraced loop body also creates a new block instance on each pass

```c filename=example.c
struct pair { int left; int right; };
int answer(void) {
    int i = 0;
    struct pair *p = 0;
    while (i < 2) p = &(struct pair){i++,22};
    return i;
}
```

```click
verifying "example.c";
int32 answer() { ensures result == 2; } by {
    step(); step(); step(); step();
    loop { decreases 2 - i; invariant 0 <= i and i <= 2; }
}
```

```expect
pass
```
