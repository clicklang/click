# A loop frame keeps a two-hop map beside a written array

`clear_data` reaches the arena through its region descriptor, copies the
pointer into a local, and clears `arena->data` in a loop that owns only that
array. The loop invariant frames the occupancy map through both hops of the
descriptor, `region->arena->occupied[k] == old(region->arena->occupied[k])`,
and the preservation proof carries it across the store with an explicit
`transport`. Closing the invariants respells the quantified frame member at
the function entry, where the inner `region->arena` load has no surface
spelling of its own; a closer that gives up on that member, or spells it
wrongly, fails to close the bundle.

```c filename=loop_frame_keeps_a_two_hop_map_beside_a_written_array.c
struct arena {
    int32* data;
    int32* occupied;
    int32 capacity;
};

struct region {
    struct arena* arena;
};

void clear_data(struct region* region) {
    struct arena* arena;
    int32 i;
    arena = region->arena;
    i = 0;
    while (i < arena->capacity) {
        arena->data[i] = 0;
        i = i + 1;
    }
}
```

```click
verifying "loop_frame_keeps_a_two_hop_map_beside_a_written_array.c";

void clear_data(struct region* region) {
    owns *region;
    owns *region->arena;
    owns region->arena->data[0..region->arena->capacity];
    owns region->arena->occupied[0..region->arena->capacity];
    requires 0 <= region->arena->capacity;
} by {
    step();
    step();
    step();
    step();
    loop {
        decreases (arena->capacity - i);
        owns arena->data[0..arena->capacity];
        invariant 0 <= i and i <= arena->capacity;
        invariant forall (k: int32) { 0 <= k and k < arena->capacity implies region->arena->occupied[k] == old(region->arena->occupied[k]) };
        initialize by simp;
        preserve by {
            mark opened;
            step();
            step();
            have forall (k: int32) { 0 <= k and k < arena->capacity implies region->arena->occupied[k] == old(region->arena->occupied[k]) } by {
                intro();
                intro();
                have at(opened, region->arena->occupied[k]) == old(region->arena->occupied[k]) by {
                    instantiate(forall (j: int32) { at(opened, 0) <= at(opened, j) and at(opened, j) < at(opened, arena->capacity) implies at(opened, region->arena->occupied[j]) == old(region->arena->occupied[j]) }, k);
                    assumption();
                }
                transport(at(opened, region->arena->occupied[k]) == old(region->arena->occupied[k]), region->arena->occupied[k] == old(region->arena->occupied[k])) using {
                    at(opened, region->arena->occupied[k]) == old(region->arena->occupied[k]);
                }
            }
            simp();
        }
    }
    step();
    simp();
}
```

```expect
pass
```
