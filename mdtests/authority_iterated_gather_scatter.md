# Iterated ownership gathers and scatters

Gathering and scattering regroup owned memory only; they create, move or
retire no population member, so they apply as ordinary memory steps.

```c filename=iterated_ownership_gather_scatter.c
void init_cells(int32* data, int32* occupied, int32 capacity) {
    int32 i;
    i = 0;
    while (i < capacity) {
        occupied[i] = 0;
        i = i + 1;
    }
}

void init_full(int32* data, int32* occupied, int32 capacity) {
    int32 i;
    i = 0;
    while (i < capacity) {
        occupied[i] = 1;
        i = i + 1;
    }
}
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

verifying "iterated_ownership_gather_scatter.c";

void init_cells(int32* data, int32* occupied, int32 capacity) {
    requires 0 <= capacity;
    consumes occupied[0..capacity];
    consumes data[0..capacity];
    produces arena_cells(data, occupied, capacity);
} by {
    step();
    step();
    loop {
        decreases capacity - i;
        invariant 0 <= i and i <= capacity;
        invariant forall (k: int32) {
            0 <= k and k < i implies occupied[k] == 0
        };
        owns occupied[0..capacity];
    }
    have i == capacity;
    have forall (k: int32) {
        0 <= k and k < capacity implies occupied[k] == 0
    } by {
        rewrite(capacity == i);
        assumption();
    }
    gather(arena_cells(data, occupied, capacity));
    scatter(arena_cells(data, occupied, capacity));
    gather(arena_cells(data, occupied, capacity));
    fold(arena_cells(data, occupied, capacity));
    execute();
    simp();
}

void init_full(int32* data, int32* occupied, int32 capacity) {
    requires 0 <= capacity;
    consumes occupied[0..capacity];
    produces arena_cells(data, occupied, capacity);
} by {
    step();
    step();
    loop {
        decreases capacity - i;
        invariant 0 <= i and i <= capacity;
        invariant forall (k: int32) {
            0 <= k and k < i implies occupied[k] == 1
        };
        owns occupied[0..capacity];
    }
    have i == capacity;
    have forall (k: int32) {
        0 <= k and k < capacity implies occupied[k] == 1
    } by {
        rewrite(capacity == i);
        assumption();
    }
    gather(arena_cells(data, occupied, capacity));
    fold(arena_cells(data, occupied, capacity));
    execute();
    simp();
}
```

```expect
pass
```
