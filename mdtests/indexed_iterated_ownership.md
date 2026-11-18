# Indexed unfold and fold select a guarded ownership slot

The resource's clause supplies the two-cell range for the index. The proof
saves the resource arguments before C changes the pointer. It opens and
restores the slot using the current index and the saved resource arguments.

```c filename=indexed_iterated_ownership.c
void update_slot(int *data, int *free_slots, int capacity, int i) {
    i = 0;
    data = 0;
}
```

```click
resource arena_slots(data: int32*, free_slots: int32*, capacity: int32) {
    owns free_slots[0..capacity];
    forall (k: int32) where 0 <= k and k < capacity {
        if free_slots[k] == 1 {
            owns data[2 * k..2 * k + 2];
        }
    }
}

verifying "indexed_iterated_ownership.c";

void update_slot(int32* data, int32* free_slots, int32 capacity, int32 i) {
    requires i == 1;
    requires 0 < capacity;
    owns arena_slots(data, free_slots, capacity);
    requires free_slots[0] == 1;
} by {
    unfold(arena_slots(data, free_slots, capacity));
    mark opened;
    step();
    unfold(arena_slots(data, free_slots, capacity)[i]);
    step();
    fold(at(opened, arena_slots(data, free_slots, capacity))[i]);
    fold(arena_slots(old(data), free_slots, capacity));
}
```

```expect
pass
```
