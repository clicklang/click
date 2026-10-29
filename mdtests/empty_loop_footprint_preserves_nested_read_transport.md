# Empty loop footprints do not obstruct explicit nested-read transport
```c filename=probe.c
struct arena { int32 *data; int32 *occupied; int32 capacity; };
void fill(struct arena *arena, int32 start, int32 end) {
    int32 i = start;
    while (i < end) {
        arena->occupied[i] = 1;
        return;
    }
}
```
```click
resource arena_window(
    data: int32*,
    occupied: int32*,
    capacity: int32,
    start: int32,
    end: int32
) {
    field next: int32;
    owns occupied[0..capacity];
    owns data[start..start];
    fact 0 <= start;
    fact start <= next;
    fact next <= end;
    fact end <= capacity;
    fact forall (k: int32) {
        next <= k and k < end implies occupied[k] == 0
    };
}

resource state(arena: struct arena*, start: int32, end: int32) {
    owns *arena;
    owns arena->occupied[0..arena->capacity];
    fact 0 <= start;
    fact start <= end;
    fact end <= arena->capacity;
    fact forall (k: int32) { start <= k and k < end implies arena->occupied[k] == 0 };
    fact separate(memory(*arena), memory(arena->data[0..arena->capacity]));
    fact separate(memory(*arena), memory(arena->occupied[0..arena->capacity]));
}
verifying "probe.c";
void fill(struct arena *arena, int32 start, int32 end) {
    consumes state(arena, start, end);
} by {
    unfold(state(arena, start, end));
    step(); step();
    let w = fold(arena_window(arena->data, arena->occupied, arena->capacity, start, end), { next: start });
    loop as mark_free_run {
        decreases to_integer(end) - to_integer(i);
        owns w: arena_window(arena->data, arena->occupied, arena->capacity, start, end);
        invariant w.next == i;
        invariant arena->data == old(arena->data);
        invariant arena->occupied == old(arena->occupied);
        initialize by solve();
        preserve by {
            let { next: m } = unfold(w);
            have m == i;
            have i < end;
            have end <= arena->capacity;
            have 0 <= i;
            have i < arena->capacity;
            mark opened;
            step();
            transport(at(opened, arena->occupied) == old(arena->occupied),
                      arena->occupied == old(arena->occupied)) using {
                at(opened, arena->occupied) == old(arena->occupied);
                at(opened, separate(memory(*arena), memory(arena->occupied[0..arena->capacity])));
                at(opened, separate(memory(*arena), memory(arena->data[0..arena->capacity])));
                0 <= at(opened, i);
                at(opened, i) < at(opened, arena->capacity);
            };
            have forall (k: int32) {
                at(opened, i) < k and k < end implies
                    arena->occupied[k] == 0
            } by {
                intro();
                intro();
                extract(at(opened, i) < k);
                extract(k < end);
                have at(opened, i) <= k;
                have m <= k;
                have at(opened, arena->occupied[k]) == 0 by {
                    instantiate(forall (j: int32) {
                        at(opened, m) <= at(opened, j) and
                            at(opened, j) < at(opened, end) implies
                            at(opened, arena->occupied[j]) == at(opened, 0)
                    }, k) using {
                        m <= k;
                        k < end;
                    };
                    assumption();
                }
                have 0 <= k;
                have k < at(opened, arena->capacity);
                transport(
                    at(opened, arena->occupied[k]) == 0,
                    arena->occupied[k] == 0
                ) using {
                    at(opened, arena->occupied) == old(arena->occupied);
                    arena->occupied == old(arena->occupied);
                    at(opened, separate(memory(*arena), memory(arena->occupied[0..arena->capacity])));
                    at(opened, separate(memory(*arena), memory(arena->data[0..arena->capacity])));
                    at(opened, arena->occupied[k]) == 0;
                    at(opened, i) < k;
                    0 <= at(opened, i);
                    at(opened, i) < at(opened, arena->capacity);
                    0 <= k;
                    k < at(opened, arena->capacity);
                };
                assumption();
            }
            step();
        }
    }
}
```
```expect
pass
```
