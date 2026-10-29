# A saved pointer does not permit taking the same element twice

```c filename=take_refuses_an_element_already_taken_out.c
void touch(int32* data, int32* occupied, int32 capacity, int32 index, int32 j) { }
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

verifying "take_refuses_an_element_already_taken_out.c";

void touch(int32* data, int32* occupied, int32 capacity, int32 index, int32 j) {
    owns arena_cells(data, occupied, capacity);
    requires 0 <= index;
    requires index < capacity;
    requires occupied[index] == 0;
    requires 0 <= j;
    requires j < capacity;
    requires occupied[j] == 0;
} by {
    unfold(arena_cells(data, occupied, capacity));
    take(old(data)[index..index + 1]);
    take(old(data)[j..j + 1]);
    give(data[index..index + 1]);
    give(data[j..j + 1]);
    fold(arena_cells(data, occupied, capacity));
}
```

```expect
fail: this element may already be taken out
```
