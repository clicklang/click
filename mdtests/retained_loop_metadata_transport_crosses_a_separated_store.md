# Explicit field transport after a store inside an ownership loop
```c filename=probe.c
struct arena { int32* data; int32* occupied; int32 capacity; };
struct region { struct arena* arena; int32 start; int32 end; };
void clear(struct region* region) {
    struct arena* arena = region->arena;
    int32 i = region->start;
    while (i < region->end) {
        arena->occupied[i] = 0;
        return;
    }
}
```
```click
resource arena_clear_window(
    data: int32*,
    occupied: int32*,
    capacity: int32,
    start: int32,
    end: int32
) {
    field next: int32;
    owns occupied[0..capacity];
    owns data[next..end];
    fact 0 <= start;
    fact start <= next;
    fact next <= end;
    fact end <= capacity;
    fact separate(memory(occupied[0..capacity]), memory(data[0..capacity]));
    fact forall (k: int32) {
        start <= k and k < next implies occupied[k] == 0
    };
}

verifying "probe.c";
void clear(struct region* region) {
    owns *region;
    owns *region->arena;
    consumes w: arena_clear_window(region->arena->data, region->arena->occupied,
        region->arena->capacity, region->start, region->end);
    requires w.next == region->start;
    requires separate(memory(*region), memory(region->arena->occupied[0..region->arena->capacity]));
} by {
    step(); step(); step(); step();
    loop as scan {
        decreases to_integer(region->end) - to_integer(i);
        owns w: arena_clear_window(arena->data, arena->occupied, arena->capacity, region->start, region->end);
        invariant w.next == i;
        invariant separate(memory(*region), memory(arena->occupied[0..arena->capacity]));
        initialize by solve();
        preserve by {
            let { next: m } = unfold(w);
            have m == i;
            have 0 <= i;
            have i < arena->capacity;
            mark opened;
            step();
            transport(at(opened, region->start) == at(opened, region->start),
                      region->start == at(opened, region->start)) using {
                at(opened, separate(memory(*region), memory(arena->occupied[0..arena->capacity])));
                0 <= at(opened, i);
                at(opened, i) < at(opened, arena->capacity);
            };
            step();
        }
    }
}
```
```expect
pass
```
