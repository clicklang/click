# Cleanup retires both pool authorities after consuming all slots

The C implementation is unchanged from `examples/bounded-pool/pool_destroy.c`.
The entry capacity is arbitrary, including zero. Cleanup consumes every owned
slot and checks both populations are empty before retiring their authorities.

```c filename=pool_destroy.c
struct pool {
    int32 checked_out;
    int32 capacity;
};

void pool_destroy(struct pool* pool) {
    pool->capacity = 0;
}
```

```c filename=payload.c
struct object { int32 value; };
```

```click resource_semantics=authority
authorized resource pool_slot(pool: struct pool*) {}
authorized resource pool_object(pool: struct pool*, object: struct object*) { owns *object; }
resource pool_control(pool: struct pool*) {
    owns *pool;
    owns authority(pool_slot(pool));
    owns authority(pool_object(pool, _));
    fact 0 <= pool->checked_out;
    fact pool->checked_out == count(pool_object(pool, _));
    fact pool->capacity == pool->checked_out + count(pool_slot(pool));
}
predicate valid_pool(pool: struct pool*) {
    0 <= pool->checked_out and
    pool->checked_out == count(pool_object(pool, _)) and
    pool->capacity == pool->checked_out + count(pool_slot(pool))
}
verifying "pool_destroy.c";
verifying "payload.c";
void pool_destroy(struct pool* pool) {
    consumes pool_control(pool);
    consumes pool->capacity of pool_slot(pool);
    requires pool->checked_out == 0;
    produces *pool;
    ensures pool->checked_out == 0;
    ensures pool->capacity == 0;
    ensures count(pool_slot(pool)) == 0;
    ensures count(pool_object(pool, _)) == 0;
    ensures valid_pool(pool);
} by {
    unfold(pool_control(pool));
    have count(pool_object(pool, _)) == 0 by simp;
    have pool->capacity == count(pool_slot(pool)) by simp;
    unfold(pool->capacity of pool_slot(pool));
    have count(pool_slot(pool)) == 0 by simp;
    step();
    unfold(authority(pool_slot(pool)));
    unfold(authority(pool_object(pool, _)));
    execute(); unfold(valid_pool); simp();
}
```

```expect
pass
```
