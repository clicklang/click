# Loop entry keeps unfolded state fields beside its owned map

`mark_all` unfolds a folded `state` that owns the arena's fields and
separates them from the occupancy map, then runs a loop that declares only
the map. The fields the function keeps cannot be written by the loop, so at
loop entry their cells are reinstalled whole into the loop's framed memory.
This catches a loop frame that drops or misplaces the kept field cells, which
the loop's bound `arena->capacity` is read from on every iteration.

```c filename=loop_entry_keeps_unfolded_state_fields_beside_its_owned_map.c
struct arena {
    int32* occupied;
    int32 capacity;
};

void mark_all(struct arena* arena) {
    int32 i;
    i = 0;
    while (i < arena->capacity) {
        arena->occupied[i] = 1;
        i = i + 1;
    }
}
```

```click
resource state(arena: struct arena*) {
    owns arena->occupied;
    owns arena->capacity;
    fact separate(
        memory(*arena),
        memory(arena->occupied[0..arena->capacity])
    );
}

verifying "loop_entry_keeps_unfolded_state_fields_beside_its_owned_map.c";

void mark_all(struct arena* arena) {
    owns state(arena);
    owns arena->occupied[0..arena->capacity];
    requires 0 <= arena->capacity;
} by {
    unfold(state(arena));
    step();
    step();
    loop as mark {
        decreases (arena->capacity - i);
        owns arena->occupied[0..arena->capacity];
        invariant 0 <= i and i <= arena->capacity;
        initialize by simp;
        preserve by {
            step();
            step();
            simp();
        }
    }
    step();
    fold(state(arena));
    simp();
}
```

```expect
pass
```
