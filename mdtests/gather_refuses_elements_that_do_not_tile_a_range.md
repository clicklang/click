# `gather` refuses elements that do not tile one range

`gather` forms an iterated ownership fact from the one owned range its
elements cover. Here each index owns `data[2 * k..2 * k + 1]`, one cell of
every two, so the elements leave gaps and no single range is their union:
`gather` is refused even though every guard is known true and the whole
`data[0..capacity * 2]` is owned. A tiling clause (`data[2 * k..2 * k + 2]`)
gathers from the same range; with every guard known false, `gather` forms
the gapped fact from nothing.

```c filename=gather_refuses_elements_that_do_not_tile_a_range.c
void touch(int32* data, int32* occupied, int32 capacity) { }
```

```click
resource evens(data: int32*, occupied: int32*, capacity: int32) {
    owns occupied[0..capacity];
    forall (k: int32) where 0 <= k and k < capacity {
        if occupied[k] == 0 {
            owns data[2 * k..2 * k + 1];
        }
    }
}

verifying "gather_refuses_elements_that_do_not_tile_a_range.c";

void touch(int32* data, int32* occupied, int32 capacity) {
    requires 0 <= capacity;
    requires capacity < 1000;
    owns occupied[0..capacity];
    owns data[0..capacity * 2];
    requires forall (k: int32) { 0 <= k and k < capacity implies occupied[k] == 0 };
} by {
    gather(evens(data, occupied, capacity));
    scatter(evens(data, occupied, capacity));
    execute();
    simp();
}
```

```expect
fail: the elements do not tile one range
```
