# An allocation identity keeps its name after reassignment

The allocation's source region names the fresh heap identity after its local is
reassigned. Casts of the identity and its byte offsets name typed pointers
and ranges. The name does not keep freed memory live.

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
    have statement(1).result == p by close();
    branch { true => { step(); } false => {} }
    have statement(1).allocation == p;
    have statement(1).allocation != 0;
    have (statement(1).allocation as (void *)) as (int32 *) == p by close();
    have (byte_offset(statement(1).allocation, 4) as (void *)) as (int32 *) == p + 1 by close();
    have contains(
        memory(p[0..1]),
        memory(((statement(1).allocation as (void *)) as (int32 *))[0..1])
    ) by close();
    step();
    step();
    have statement(1).allocation != 0 by close();
}
```

```expect
pass
```
