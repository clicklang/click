# A post-return fold retains the readability of a stored cell

Reduced from `arena_write`: the symbolic store materializes one cell within
a larger owned interval. Its exact-width read validity is intrinsic to that
memory state. A post-return quantified proof followed by resource folds
must not lose that fact during certification. The C is the unchanged arena
write function.

```c filename=arena_write.c
struct arena {
    int32* data;
    int32* occupied;
    int32 capacity;
    int32 live_regions;
};

struct region {
    struct arena* arena;
    int32 start;
    int32 end;
};

void arena_write(struct region* region, int32 index, int32 value) {
    struct arena* arena;

    arena = region->arena;
    arena->data[region->start + index] = value;
}
```
```click
import click::separation;

resource arena_initialized_storage(
    data: int32*,
    occupied: int32*,
    capacity: int32,
    initialized: int32
) {
    if initialized == 1 {
        owns allocation(data, capacity * 4);
        owns allocation(occupied, capacity * 4);
        fact 1 <= capacity;
        fact capacity <= 536870911;
    }
}

resource arena_cells(data: int32*, occupied: int32*, capacity: int32) {
    owns occupied[0..capacity];
    forall (k: int32) where 0 <= k and k < capacity {
        if occupied[k] == 0 {
            owns data[k..k + 1];
        }
    }
}

resource arena_state(arena: struct arena*) {
    field live: int32;
    field capacity: int32;
    owns arena->data;
    owns arena->occupied;
    owns arena->capacity;
    owns arena->live_regions;
    owns arena_initialized_storage(
        arena->data,
        arena->occupied,
        arena->capacity,
        1
    );
    owns arena_cells(arena->data, arena->occupied, arena->capacity);
    fact arena->capacity <= 536870911;
    fact arena->capacity == capacity;
    fact arena->live_regions == live;
    fact 0 <= live;
    fact separate(
        memory(arena->occupied[0..arena->capacity]),
        memory(arena->data[0..arena->capacity])
    );
    fact separate(
        memory(*arena),
        memory(arena->data[0..arena->capacity])
    );
    fact separate(
        memory(*arena),
        memory(arena->occupied[0..arena->capacity])
    );
}

resource arena_region(region: struct region*) {
    field start: int32;
    field end: int32;
    owns *region;
    owns region->arena->data[start..end];
    fact region->start == start;
    fact region->end == end;
    fact 0 <= start;
    fact start < end;
}

verifying "arena_write.c";

void arena_write(struct region* region, int32 index, int32 value) {
    owns r: arena_region(region);
    owns st: arena_state(old(region->arena));
    requires 0 <= index;
    requires defined(r.start + index) and to_integer(r.start + index) < to_integer(r.end);
    requires r.end <= st.capacity;

    ensures r.start == old(r.start);
    ensures r.end == old(r.end);
    ensures st.capacity == old(st.capacity);
    ensures r.end <= st.capacity;
    ensures st.live == old(st.live);
    ensures region->arena == old(region->arena);
    ensures region->arena->capacity == old(region->arena->capacity);
    ensures region->arena->data == old(region->arena->data);
    ensures region->arena->data[region->start + index] == value;
    ensures region->arena->data[r.start + index] == value;
    ensures forall (k: int32) {
        0 <= k and k < region->arena->capacity implies
            region->arena->occupied[k] == old(region->arena->occupied[k])
    };
} by {
    let { live: n, capacity: c } = unfold(st);
    let { start: s, end: e } = unfold(r);
    have defined(s + index) by {
        close() using {
            defined(s + index) and to_integer(s + index) < to_integer(e);
        };
    }
    have to_integer(s + index) < to_integer(e) by {
        close() using {
            defined(s + index) and to_integer(s + index) < to_integer(e);
        };
    }
    have to_integer(s) <= to_integer(s + index);
    have to_integer(s + index + 1) <= to_integer(e);
    have region->start == s by {
        close();
    }
    have defined(region->start);
    have defined(region->start + index) by {
        rewrite(region->start, s);
        close();
    }
    have to_integer(region->start) <= to_integer(region->start + index) by {
        rewrite(region->start, s);
        close();
    }
    have defined(s + index + 1);
    have defined(region->start + index + 1) by {
        rewrite(region->start, s);
        close();
    }
    have to_integer(region->start + index + 1) <= to_integer(e) by {
        rewrite(region->start, s);
        close();
    }
    have 0 <= to_integer(region->start + index) by {
        rewrite(region->start, s);
        have 0 <= to_integer(s + index);
        close();
    }
    have to_integer(s + index) < to_integer(c);
    have region->arena->capacity == c by {
        close();
    }
    have to_integer(region->start + index) < to_integer(region->arena->capacity) by {
        rewrite(region->start, s);
        rewrite(region->arena->capacity, c);
        close();
    }
    mark w;
    step();
    have separate(statement(0).footprint, memory(region->arena)) by { close() using {}; }
    have region->arena == at(statement(0).entry, region->arena) by {
        preserve(memory(region->arena), statement(0));
    }
    have separate(statement(0).footprint, memory(region->arena->data)) by { close() using {}; }
    have region->arena->data == at(statement(0).entry, region->arena->data) by {
        preserve(memory(region->arena->data), statement(0));
    }
    have separate(statement(0).footprint, memory(region->arena->occupied)) by { close() using {}; }
    have region->arena->occupied == at(statement(0).entry, region->arena->occupied) by {
        preserve(memory(region->arena->occupied), statement(0));
    }
    step();
    have separate(statement(1).footprint, memory(region->arena)) by { close() using {}; }
    have region->arena == at(statement(1).entry, region->arena) by {
        preserve(memory(region->arena), statement(1));
    }
    have separate(statement(1).footprint, memory(region->arena->data)) by { close() using {}; }
    have region->arena->data == at(statement(1).entry, region->arena->data) by {
        preserve(memory(region->arena->data), statement(1));
    }
    have separate(statement(1).footprint, memory(region->arena->occupied)) by { close() using {}; }
    have region->arena->occupied == at(statement(1).entry, region->arena->occupied) by {
        preserve(memory(region->arena->occupied), statement(1));
    }
    mark before_access;
    have at(before_access, separate(memory(region->arena->data[region->start + index]), memory(region->arena)));
    have at(before_access, separate(memory(region->arena->data[region->start + index]), memory(region->arena->data)));
    have at(before_access, separate(memory(region->arena->data[region->start + index]), memory(region->arena->occupied)));
    have at(before_access, separate(memory(region->arena->data[region->start + index]), memory(region->arena->capacity)));
    step();
    have separate(statement(2).footprint, memory(region->arena->capacity)) by {
        close() using { at(before_access, separate(memory(region->arena->data[region->start + index]), memory(region->arena->capacity))); };
    }
    have region->arena->capacity == at(before_access, region->arena->capacity) by {
        preserve(memory(region->arena->capacity), statement(2));
    }
    have separate(statement(2).footprint, memory(region->arena)) by { close() using { at(before_access, separate(memory(region->arena->data[region->start + index]), memory(region->arena))); }; }
    have region->arena == at(before_access, region->arena) by {
        preserve(memory(region->arena), statement(2));
    }
    have separate(statement(2).footprint, memory(region->arena->data)) by { close() using { at(before_access, separate(memory(region->arena->data[region->start + index]), memory(region->arena->data))); }; }
    have region->arena->data == at(before_access, region->arena->data) by {
        preserve(memory(region->arena->data), statement(2));
    }
    have separate(statement(2).footprint, memory(region->arena->occupied)) by { close() using { at(before_access, separate(memory(region->arena->data[region->start + index]), memory(region->arena->occupied))); }; }
    have region->arena->occupied == at(before_access, region->arena->occupied) by {
        preserve(memory(region->arena->occupied), statement(2));
    }

    have region->arena == old(region->arena);
    have region->arena->data == old(region->arena->data);

    have forall (k: int32) {
        0 <= k and k < at(w, region->arena->capacity) implies
            at(w, region->arena->occupied[k]) == region->arena->occupied[k]
    } by {
        intro() {
            intro() {
                have 0 <= k;
                have k < at(w, region->arena->capacity);
                have k < region->arena->capacity by { close(); }
                have contains(memory(region->arena->occupied[0..region->arena->capacity]), memory(region->arena->occupied[k])) by {
                    apply(separation::contains_element(region->arena->occupied, 0, region->arena->capacity, k));
                }
                have 0 <= at(before_access, region->start + index) by { close(); }
                have at(before_access, region->start + index) < region->arena->capacity by { close(); }
                have 0 <= to_integer(at(before_access, region->start + index)) by { close(); }
                have to_integer(at(before_access, region->start + index)) < to_integer(region->arena->capacity) by { close(); }
                have at(before_access, region->arena->data) == region->arena->data by { close(); }
                have contains(memory(at(before_access, region->arena->data)[0..region->arena->capacity]), memory(at(before_access, region->arena->data)[at(before_access, region->start + index)])) by {
                    apply(separation::contains_element(at(before_access, region->arena->data), 0, region->arena->capacity, at(before_access, region->start + index)));
                }
                have contains(memory(region->arena->data[0..region->arena->capacity]), memory(at(before_access, region->arena->data)[at(before_access, region->start + index)])) by { rewrite(region->arena->data, at(before_access, region->arena->data)); close(); }
                have separate(memory(at(before_access, region->arena->data)[at(before_access, region->start + index)]), memory(region->arena->occupied[k])) by {
                    apply(separation::separate_symm(memory(region->arena->occupied[0..region->arena->capacity]), memory(region->arena->data[0..region->arena->capacity])));
                    apply(separation::separate_restrict(
                        memory(region->arena->data[0..region->arena->capacity]),
                        memory(region->arena->occupied[0..region->arena->capacity]),
                        memory(at(before_access, region->arena->data)[at(before_access, region->start + index)]),
                        memory(region->arena->occupied[k])
                    ));
                }
                have separate(statement(0).footprint, memory(region->arena->occupied[k])) by { close() using {}; }
                have at(statement(0).exit, region->arena->occupied[k]) == at(statement(0).entry, region->arena->occupied[k]) by {
                    preserve(memory(region->arena->occupied[k]), statement(0));
                }
                have separate(statement(1).footprint, memory(region->arena->occupied[k])) by { close() using {}; }
                have at(statement(1).exit, region->arena->occupied[k]) == at(statement(1).entry, region->arena->occupied[k]) by {
                    preserve(memory(region->arena->occupied[k]), statement(1));
                }
                have separate(statement(2).footprint, memory(region->arena->occupied[k])) by { close() using { separate(memory(at(before_access, region->arena->data)[at(before_access, region->start + index)]), memory(region->arena->occupied[k])); }; }
                have at(statement(2).exit, region->arena->occupied[k]) == at(statement(2).entry, region->arena->occupied[k]) by {
                    preserve(memory(region->arena->occupied[k]), statement(2));
                }
                close();
            }
        }
    }
    have region->arena->capacity == old(region->arena->capacity) by close();
    have separate(memory(*region->arena), memory(region->arena->data[0..region->arena->capacity])) by {
        rewrite(region->arena->capacity, old(region->arena->capacity));
        rewrite(region->arena->data, old(region->arena->data));
        rewrite(region->arena, old(region->arena));
        close();
    }
    have region->arena->occupied == old(region->arena->occupied) by close();
    have separate(memory(*region->arena), memory(region->arena->occupied[0..region->arena->capacity])) by {
        rewrite(region->arena->capacity, old(region->arena->capacity));
        rewrite(region->arena->occupied, old(region->arena->occupied));
        rewrite(region->arena, old(region->arena));
        close();
    }
    have separate(memory(region->arena->occupied[0..region->arena->capacity]), memory(region->arena->data[0..region->arena->capacity])) by {
        rewrite(region->arena->capacity, old(region->arena->capacity));
        rewrite(region->arena->occupied, old(region->arena->occupied));
        rewrite(region->arena->data, old(region->arena->data));
        close();
    }
    let r = fold(arena_region(region), { start: s, end: e });
    let st = fold(arena_state(region->arena), { live: n, capacity: c });
    step_until(function.exit);
    close();
}

```
```expect
pass
```
