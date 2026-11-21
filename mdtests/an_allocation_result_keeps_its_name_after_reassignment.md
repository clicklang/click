# An allocation identity keeps its name after reassignment

The allocation's source region names the fresh heap identity after its local is
reassigned. The name is a value observation and does not keep freed memory live.

```c filename=allocation.c
int32 use_allocation() {
    int32* p;
    p = malloc(4);
    if (p == 0) return 0;
    free(p);
    p = 0;
    return 0;
}
```

```click
verifying "allocation.c";
int32 use_allocation() { ensures result == 0; } by {
    step();
    step();
    have statement(1).result == p by known();
    branch { true => { step(); } false => {} }
    have statement(1).allocation == p;
    have statement(1).allocation != 0;
    step();
    step();
    have statement(1).allocation != 0 by known();
}
```

```expect
pass
```
