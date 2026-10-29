# A saved pointer does not bypass a false current guard

```c filename=iterated_ownership_rejects_give_false_guard.c
void release(int32* data, int32* occupied, int32 capacity, int32 index) {
    occupied[index] = 1;
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

verifying "iterated_ownership_rejects_give_false_guard.c";

void release(int32* data, int32* occupied, int32 capacity, int32 index) {
    owns arena_cells(data, occupied, capacity);
    requires 0 <= index;
    requires index < capacity;
    requires occupied[index] == 0;
} by {
    unfold(arena_cells(data, occupied, capacity));
    take(old(data)[index..index + 1]);
    step();
    give(old(data)[index..index + 1]);
    fold(arena_cells(data, occupied, capacity));
}
```

```expect
fail: the guard is false at this index
```
