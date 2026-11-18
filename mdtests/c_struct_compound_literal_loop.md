# A literal in a loop block is initialized and retired on each pass

```c filename=example.c
struct pair { int left; int right; };
int answer(void) {
    int i = 0;
    while (i < 2) {
        struct pair *p = &(struct pair){i, 22};
        i = p->left + 1;
    }
    return i;
}
```

```click
verifying "example.c";
int32 answer() { ensures result == 2; } by {
    step(); step();
    loop { decreases 2 - i; invariant 0 <= i and i <= 2; }
}
```

```expect
pass
```
