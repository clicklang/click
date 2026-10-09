# Explicit transport refuses an unproved frame promptly

The write is owned by the region, but its start is not known to lie in the
arena's separated data range. The saved occupancy read therefore has no frame
evidence. A single explicit transport must reuse identical failed memory
questions across its bridge, reachability, and quantified-frame routes.
The fixture harness pins this refusal below the work needed without that reuse.

```c filename=explicit_transport_failure_is_prompt.c
struct arena {
    int32* data;
    int32* occupied;
    int32 capacity;
};

struct region {
    struct arena* arena;
    int32 start;
    int32 end;
};

void arena_write(struct region* region, int32 value, int32 k) {
    struct arena* arena;

    arena = region->arena;
    arena->data[region->start] = value;
}
```

```click
resource arena_state(arena: struct arena*) {
    field capacity: int32;
    owns arena->data;
    owns arena->occupied;
    owns arena->capacity;
    owns arena->occupied[0..arena->capacity];
    fact arena->capacity <= 536870911;
    fact arena->capacity == capacity;
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
    fact start < end;
}

verifying "explicit_transport_failure_is_prompt.c";

void arena_write(struct region* region, int32 value, int32 k) {
    owns r: arena_region(region);
    owns st: arena_state(old(region->arena));
    requires r.end <= st.capacity;
    requires 0 <= k and k < st.capacity;
} by {
    let { capacity: c } = unfold(st);
    let { start: s, end: e } = unfold(r);
    have s + 1 <= e by {
        apply(int32_increment_upper_bound(s, e)) using { s < e; }
    }
    have region->start + 1 <= e by {
        rewrite(region->start == s); assumption();
    }
    mark w;
    execute();
    have at(w, region->arena->occupied[k]) == region->arena->occupied[k] by {
        transport(at(w, region->arena->occupied[k]) == at(w, region->arena->occupied[k]),
            at(w, region->arena->occupied[k]) == region->arena->occupied[k]) using {};
    }
}
```

```expect
fail: found no frame evidence
```
