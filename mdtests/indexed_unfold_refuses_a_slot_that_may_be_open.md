# Indexed `unfold` refuses an element that may already be taken out

indexed `unfold` moves one element out of an unfolded iterated ownership fact, and the
fact then claims nothing at that index. A second indexed `unfold` must show its index
differs from every index already out. Here `j` is in range and its guard is
known true, but nothing says `j != index`, so `unfold(arena_cells(data, occupied, capacity)[j])` is
refused: it may name the element the first indexed `unfold` already moved. With
`requires j != index;` both elements come out
(the condition decision then separates the two indices).

```c filename=indexed_unfold_refuses_a_slot_that_may_be_open.c
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

verifying "indexed_unfold_refuses_a_slot_that_may_be_open.c";

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
    unfold(arena_cells(data, occupied, capacity)[index]);
    unfold(arena_cells(data, occupied, capacity)[j]);
    fold(arena_cells(data, occupied, capacity)[index]);
    fold(arena_cells(data, occupied, capacity)[j]);
    fold(arena_cells(data, occupied, capacity));
}
```

```expect
fail: this element may already be taken out
```
