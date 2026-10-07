# A byte stored inside a calloc'd pointer cell makes that pointer non-null

The byte store at offset 3 overwrites one byte of the pointer cell at offset
0, so `q[0]` no longer reads as the null pointer `calloc` gave it.

```c filename=calloc_byte_store_inside_pointer_cell_is_not_null.c
int32 f() {
    int32** q = calloc(2, sizeof(int32*));
    if (q == 0) { return 1; }
    uint8* b = (uint8*)(void*) q;
    b[3] = 9;
    int32 r = 0;
    if (q[0] == 0) { r = 1; }
    free(q);
    return r;
}
```

```click
verifying "calloc_byte_store_inside_pointer_cell_is_not_null.c";

int32 f() {
    ensures result == 1;
} by {
    execute();
    simp();
}
```

```expect
fail: result == 1; left side evaluated to 0
```
