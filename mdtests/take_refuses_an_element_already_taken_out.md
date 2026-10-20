# `take` refuses an element that may already be taken out

`take` moves one element out of an unfolded iterated ownership fact, and the
fact then claims nothing at that index. A second `take` must show its index
differs from every index already out. Here `j` is in range and its guard is
known true, but nothing says `j != index`, so `take(data[j..j + 1])` is
refused: it may name the element the first `take` already moved. With
`requires j != index;` both elements come out
(the condition decision then separates the two indices).

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
    take(data[index..index + 1]);
    take(data[j..j + 1]);
    give(data[index..index + 1]);
    give(data[j..j + 1]);
    fold(arena_cells(data, occupied, capacity));
    execute();
    simp();
}
```

```expect
fail: this element may already be taken out
```
