# An indexed resource operation requires a signed 32-bit index

The value `0u64` is outside the slot index type even though the numerical
value would be in bounds.

```c filename=indexed_unfold_requires_int32_index.c
void touch(int32* data, int32* occupied, int32 capacity, int32 index) { }
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

verifying "indexed_unfold_requires_int32_index.c";

void touch(int32* data, int32* occupied, int32 capacity, int32 index) {
    owns arena_cells(data, occupied, capacity);
    requires 0 <= index;
    requires index + 1 < capacity;
    requires occupied[index] == 0;
    requires occupied[index + 1] == 0;
} by {
    unfold(arena_cells(data, occupied, capacity));
    unfold(arena_cells(data, occupied, capacity)[0u64]);
    fold(arena_cells(data, occupied, capacity));
}
```

```expect
fail: `unfold` slot index must be int32
```
