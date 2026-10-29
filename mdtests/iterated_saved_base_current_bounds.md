# Saved pointer base keeps range bounds in the current state

```c filename=iterated_ownership_release_one.c
void release(int32* data, int32* occupied, int32 capacity, int32 index) {
    index = 0;
    occupied[index] = 0;
}
```

```click
resource arena_cells(data: int32*, occupied: int32*, capacity: int32) {
    owns occupied[0..capacity];
    forall (k: int32) where 0 <= k and k < capacity {
        if occupied[k] == 0 {
            owns data[k..k + 1];
        }
    }
}

resource claimed(data: int32*, index: int32) {
    field held: int32;
    if held == 1 {
        owns data[index..index + 1];
    }
}

verifying "iterated_ownership_release_one.c";

void release(int32* data, int32* occupied, int32 capacity, int32 index) {
    owns arena_cells(data, occupied, capacity);
    consumes cell: claimed(data, 0);
    requires index == 1;
    requires 0 < capacity;
    requires cell.held == 1;
} by {
    unfold(arena_cells(data, occupied, capacity));
    unfold(cell);
    mark before;
    step();
    step();
    give(at(before, data)[index..index + 1]);
    fold(arena_cells(data, occupied, capacity));
}
```

```expect
pass
```
