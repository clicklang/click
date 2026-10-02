# Pool growth must prove machine addition is defined

The C block is unchanged from `examples/bounded-pool/pool_grow.c`.
A control at maximum capacity cannot justify growth by one.

```c filename=pool_grow.c
struct pool {
    int32 checked_out;
    int32 capacity;
};

void pool_grow(struct pool* pool, int32 amount) {
    pool->capacity = pool->capacity + amount;
}
```

```click resource_semantics=authority
resource pool_slot(pool: struct pool*) {}
resource pool_control(pool: struct pool*) {
    owns object(pool);
    owns authority(pool_slot(pool));
    fact 0 <= pool->checked_out;
    fact pool->capacity == pool->checked_out + count(pool_slot(pool));
}
verifying "pool_grow.c";
void pool_grow(struct pool* pool, int32 amount) {
    owns pool_control(pool);
    requires pool->capacity == 2147483647;
    requires amount == 1;
    produces amount of pool_slot(pool);
} by {
    open(pool_control(pool)) { step(); }
    execute();
}
```

```expect
fail: undefined behavior: signed overflow
```
