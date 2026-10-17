# An address inside an allocation is spelled from the local that held it

After `free(p)` no local holds the allocation, but `p` held it at the end of
statement 2. The refusal's goal, its premises and its proof context all name
values by what a local held at a recorded point: the value read is
`at(statement(9).exit, r)`, the freed allocation is
`at(statement(2).exit, p)`, and the byte the store changed, five bytes into
it, is `*((char *)at(statement(2).exit, p) + 5)`, rather than report-local
`<pointer A>` placeholders.

```c filename=an_allocation_element_is_spelled_from_the_local_that_held_it.c
int32 f(int32 k) {
    int32* p = calloc(4, sizeof(int32));
    if (p == 0) { return 0; }
    uint8* b = (uint8*)(void*) p;
    b[5] = 9;
    int32 r = p[k];
    free(p);
    return r;
}
```

```click
verifying "an_allocation_element_is_spelled_from_the_local_that_held_it.c";

int32 f(int32 k) {
    requires 0 <= k;
    requires k < 4;
    ensures result == 0;
} by {
    execute();
    simp();
}
```

```expect
fail: goal: at(statement(9).exit, r) == 0
```
