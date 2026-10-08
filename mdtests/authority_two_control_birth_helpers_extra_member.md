# An extra birth cannot hide inside the second returned control

The initialization C is unchanged from the bounded-pool example. The small
forwarding caller consumes two storage controls and returns both initialized
controls plus one new slot for each. Each population keeps its own authority,
count, and custody checks. No authority is created in either helper.

```c filename=pool_init.c
struct pool {
    int32 checked_out;
    int32 capacity;
};

void pool_init(struct pool* pool, int32 capacity) {
    pool->checked_out = 0;
    pool->capacity = capacity;
}
```

```c filename=pair.c
struct pool { int32 checked_out; int32 capacity; };
void pool_init(struct pool* pool, int32 capacity);
void initialize_pair(struct pool* source, struct pool* destination) {
    pool_init(source, 1);
    pool_init(destination, 1);
}
```

```click resource_semantics=authority
authorized resource pool_slot(pool: struct pool*) {}
authorized resource pool_object(pool: struct pool*, object: int32*) {}
resource pool_storage(pool: struct pool*) {
    owns *pool;
    owns authority(pool_slot(pool));
    owns authority(pool_object(pool, _));
}
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
verifying "pool_init.c";
verifying "pair.c";
void pool_init(struct pool* pool, int32 capacity) {
    consumes pool_storage(pool);
    requires 0 <= capacity;
    requires count(pool_slot(pool)) == 0;
    requires count(pool_object(pool, _)) == 0;
    produces pool_control(pool);
    produces capacity of pool_slot(pool);
    ensures pool->capacity == capacity;
    ensures pool->checked_out == 0;
    ensures count(pool_object(pool, _)) == 0;
    ensures valid_pool(pool);
} by {
    unfold(pool_storage(pool));
    step(); step();
    fold(capacity of pool_slot(pool));
    fold(pool_control(pool));
    execute(); unfold(valid_pool); simp();
}
void initialize_pair(struct pool* source, struct pool* destination) {
    requires source != destination;
    consumes pool_storage(source);
    consumes pool_storage(destination);
    requires count(pool_slot(source)) == 0;
    requires count(pool_slot(destination)) == 0;
    requires count(pool_object(source, _)) == 0;
    requires count(pool_object(destination, _)) == 0;
    produces pool_control(source);
    produces pool_control(destination);
    produces pool_slot(source);
    produces pool_slot(destination);
    ensures source->capacity == 1;
    ensures destination->capacity == 1;
    ensures count(pool_slot(source)) == 1;
    ensures count(pool_slot(destination)) == 1;
} by {
    step();
    open(pool_control(source)) { step(); }
    open(pool_control(destination)) {
        have count(pool_slot(destination)) == 1 by simp;
        have defined(count(pool_slot(destination)) + 1) by simp;
        fold(pool_slot(destination));
    }
    execute(); simp();
}
```

```expect
fail: Requires destination->capacity == (destination->checked_out + count(pool_slot(destination)))
```
