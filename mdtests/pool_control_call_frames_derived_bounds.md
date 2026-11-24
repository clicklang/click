# A pool control call frames bounds derived inside an open scope

Arithmetic search expands to ordinary proof steps, with the selected premises
stated explicitly in `close() using { ... }`.

```c filename=pool_control_call_frames.c
struct pool { int32 used; int32 capacity; };
int32 pool_used(struct pool* pool) { return pool->used; }
int32 forward(struct pool* pool) { return pool_used(pool); }
```

```click
import click::integer;

authorized resource slot(pool: struct pool*) {}
resource control(pool: struct pool*) {
    owns *pool;
    owns authority(slot(pool));
    fact defined(pool->used + count(slot(pool)));
    fact to_integer(pool->capacity) == to_integer(pool->used + count(slot(pool)));
}
theorem spare_slot_bound(capacity: int32, used: int32, slots: int32) {
    requires to_integer(capacity) == to_integer(used) + to_integer(slots);
    requires to_integer(capacity) <= 2147483647;
    requires 1 <= to_integer(used);
    ensures to_integer(slots) + 1 <= 2147483647 by {
        close() using { to_integer(capacity) == to_integer(used) + to_integer(slots); to_integer(capacity) <= 2147483647; 1 <= to_integer(used); };
    }
}
verifying "pool_control_call_frames.c";
int32 pool_used(struct pool* pool) {
    owns control(pool);
} by {
    with(control(pool)) { step_until(function.exit); }
    close();
}
int32 forward(struct pool* pool) {
    owns control(pool);
    requires 0 < pool->used;
    ensures defined(pool->used + count(slot(pool)));
} by {
    with(control(pool)) {
        have 0 <= pool->used;
        have defined(pool->used + count(slot(pool))) by { close(); }
    }
}
```

```expect
pass
```
