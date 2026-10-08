# Slot growth needs its matching authority

Owning and updating the C capacity alone cannot mint population members.
The C block is unchanged from `examples/bounded-pool/pool_grow.c`.

```c filename=pool_grow.c
struct pool {
    int32 checked_out;
    int32 capacity;
};

void pool_grow(struct pool* pool, int32 amount) {
    pool->capacity = pool->capacity + amount;
}
```

```c filename=grow_caller.c
struct pool { int32 checked_out; int32 capacity; };
void pool_grow(struct pool* pool, int32 amount);
void caller(struct pool* pool, int32 amount) { pool_grow(pool, amount); }
```

```click resource_semantics=authority
authorized resource pool_slot(pool: struct pool*) {}
verifying "pool_grow.c";
verifying "grow_caller.c";
void pool_grow(struct pool* pool, int32 amount) {
    owns *pool;
    owns authority(pool_slot(pool));
    requires defined(count(pool_slot(pool)) + amount);
    requires 0 < amount;
    requires defined(pool->capacity + amount);
    produces amount of pool_slot(pool);
} by {
    step();
    fold(amount of pool_slot(pool));
    execute(); simp();
}
void caller(struct pool* pool, int32 amount) {
    owns *pool;
    requires 0 < amount;
    requires defined(pool->capacity + amount);
    produces amount of pool_slot(pool);
} by { execute(); }
```

```expect
fail: Requires owns authority(pool_slot(...))
```
