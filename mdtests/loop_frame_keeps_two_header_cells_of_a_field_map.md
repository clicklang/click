# A loop frame keeps two header cells of a map reached through a field

`mark_tail` marks `arena->occupied[i]` from index 2 up to `end`, leaving
the two header cells `arena->occupied[0]` and `arena->occupied[1]` alone;
the loop's bound check reads the map's length through the `capacity` field.
One invariant per header cell says it keeps its entry value, and the smart
closer must discharge both back-edge members from the entry viewability of
the map, spelling the second cell at a constant displacement from the
field's pointer and guarding it by the first cell's clause. This catches a
closer that can only name the cell at the field pointer itself, or that loses
the second member when an earlier one guards it.

```c filename=loop_frame_keeps_two_header_cells_of_a_field_map.c
struct arena {
    int32* occupied;
    int32 capacity;
};

void mark_tail(struct arena* arena, int32 end) {
    int32 i;
    i = 2;
    while (i < end) {
        arena->occupied[i] = 1;
        i = i + 1;
    }
}
```

```click
verifying "loop_frame_keeps_two_header_cells_of_a_field_map.c";

void mark_tail(struct arena* arena, int32 end) {
    owns *arena;
    owns arena->occupied[0..arena->capacity];
    requires separate(
        memory(*arena),
        memory(arena->occupied[0..arena->capacity])
    );
    requires 2 <= end;
    requires end <= arena->capacity;
} by {
    step();
    step();
    loop {
        owns arena->occupied[0..arena->capacity];
        invariant 2 <= i;
        invariant i <= end;
        invariant arena->occupied[0] == old(arena->occupied[0]);
        invariant arena->occupied[1] == old(arena->occupied[1]);
        decreases end - i;
        initialize by simp;
        preserve by {
            step();
            step();
            close_invariants();
        }
    }
    execute();
    simp();
}
```

```expect
pass
```
