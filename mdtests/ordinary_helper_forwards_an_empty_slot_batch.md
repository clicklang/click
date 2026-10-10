# An ordinary helper forwards an empty slot batch

`empty` holds a pool whose capacity is zero and forwards an empty batch,
`0 of pool_slot(pool)`, to `pool_destroy`, which consumes
`pool->capacity of pool_slot(pool)`. Matching the two batch sizes at the call
places an order fact whose two sides are the same term in the context, and
the context's inconsistency scan must read it as consistent (a reflexive
non-strict order) rather than as a contradiction. It is the reduced form of
`authority_pool_control_cleanup_helper.md`'s `empty`.

```c filename=ordinary_helper_forwards_an_empty_slot_batch.c
struct pool {
    int32 checked_out;
    int32 capacity;
};

void pool_destroy(struct pool* pool) {
    pool->capacity = 0;
}

void empty(struct pool* pool) {
    pool_destroy(pool);
}
```

```click
authorized resource pool_slot(pool: struct pool*) {}
resource pool_control(pool: struct pool*) {
    owns *pool;
    owns authority(pool_slot(pool));
    fact pool->capacity == count(pool_slot(pool));
}

verifying "ordinary_helper_forwards_an_empty_slot_batch.c";

void pool_destroy(struct pool* pool) {
    consumes pool_control(pool);
    consumes pool->capacity of pool_slot(pool);
    produces *pool;
    ensures pool->capacity == 0;
} by {
    unfold(pool_control(pool));
    have pool->capacity == count(pool_slot(pool));
    unfold(pool->capacity of pool_slot(pool));
    have count(pool_slot(pool)) == 0;
    step();
    unfold(authority(pool_slot(pool)));
    execute();
    simp();
}

void empty(struct pool* pool) {
    consumes pool_control(pool);
    consumes 0 of pool_slot(pool);
    requires pool->capacity == 0;
    produces *pool;
    ensures pool->capacity == 0;
} by {
    unfold(pool_control(pool));
    have pool->capacity == count(pool_slot(pool));
    fold(pool_control(pool));
    execute();
    simp();
}
```

```expect
pass
```
