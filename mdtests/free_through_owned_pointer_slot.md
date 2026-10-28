# Free reads an owned pointer slot

```c filename=free_pointer_slot.c
void dispose(int32** slot) { free(*slot); }
```

```click
verifying "free_pointer_slot.c";
resource cell(p: int32*) { owns allocation(p, 4); owns p[0..1]; }
void dispose(int32** slot) {
    owns slot[0..1];
    consumes cell(*slot);
} by { unfold(cell(*slot)); step(); }
```

```expect
pass
```
