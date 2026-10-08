# Iterated ownership still checks its guards in authority mode

Under authority semantics `take` is the same checked memory step: taking an
element whose guard is false is still refused.

```c filename=iterated_ownership_rejects_take_false_guard.c
void poke(int32* data, int32* occupied, int32 capacity, int32 index) {
    if (occupied[index] != 0) {
        data[index] = 7;
    }
}
```

```click resource_semantics=authority
resource arena_cells(data: int32*, occupied: int32*, capacity: int32) {
    owns occupied[0..capacity];
    forall (k: int32) where 0 <= k and k < capacity {
        if occupied[k] == 0 {
            owns data[k..k + 1];
        }
    }
}

verifying "iterated_ownership_rejects_take_false_guard.c";

void poke(int32* data, int32* occupied, int32 capacity, int32 index) {
    owns arena_cells(data, occupied, capacity);
    requires 0 <= index;
    requires index < capacity;
} by {
    unfold(arena_cells(data, occupied, capacity));
    if occupied[index] != 0 {
        take(data[index..index + 1]);
        execute();
        simp();
    } else {
        execute();
        fold(arena_cells(data, occupied, capacity));
        simp();
    }
}
```

```expect
fail: the guard is false at this index
```
