# `take` refuses a range that is not one element

`take` moves exactly one element of an iterated ownership fact: the range it
names must be the clause's element at one index, here `data[k..k + 1]`. A
two-cell range `data[index..index + 2]` spans two elements, so it is refused
even though both indices are in range with true guards; take each element
with its own `take`.

```c filename=take_refuses_a_range_that_is_not_one_element.c
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

verifying "take_refuses_a_range_that_is_not_one_element.c";

void touch(int32* data, int32* occupied, int32 capacity, int32 index) {
    owns arena_cells(data, occupied, capacity);
    requires 0 <= index;
    requires index + 1 < capacity;
    requires occupied[index] == 0;
    requires occupied[index + 1] == 0;
} by {
    unfold(arena_cells(data, occupied, capacity));
    take(data[index..index + 2]);
    fold(arena_cells(data, occupied, capacity));
    execute();
    simp();
}
```

```expect
fail: the range is not one element of the iterated ownership fact
```
