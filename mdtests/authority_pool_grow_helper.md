# Symbolic slot growth composes through an ordinary helper

This reduced control relates capacity to slots. The full two-population pool
invariant is checked separately by the authority example gate. The growth C
block is unchanged from `examples/bounded-pool/pool_grow.c`; only the small
fixture's forwarding helper is synthetic. Entry slots and growth are arbitrary,
including zero, and no existing slots are required as caller inputs.

```c filename=pool_grow.c
struct pool {
    int32 checked_out;
    int32 capacity;
};

void pool_grow(struct pool* pool, int32 amount) {
    pool->capacity = pool->capacity + amount;
}
```

```c filename=grow_forward.c
struct pool { int32 checked_out; int32 capacity; };
void pool_grow(struct pool* pool, int32 amount);
void forward(struct pool* pool, int32 amount) { pool_grow(pool, amount); }
```

```click resource_semantics=authority
authorized resource slot(pool: struct pool*) {}
resource control(pool: struct pool*) {
    owns object(pool);
    owns authority(slot(pool));
    fact pool->capacity == count(slot(pool));
}
verifying "pool_grow.c";
verifying "grow_forward.c";
void pool_grow(struct pool* pool, int32 amount) {
    owns control(pool);
    requires 0 <= amount;
    requires defined(pool->capacity + amount);
    produces amount of slot(pool);
    ensures pool->capacity == old(pool->capacity) + amount;
    ensures count(slot(pool)) == old(count(slot(pool))) + amount;
    ensures pool->checked_out == old(pool->checked_out);
} by {
    open(control(pool)) {
        have count(slot(pool)) == pool->capacity by simp;
        have 0 <= count(slot(pool)) by simp;
        have 0 <= pool->capacity by {
            arithmetic() using { 0 <= count(slot(pool)); pool->capacity == count(slot(pool)); }
        }
        have defined(count(slot(pool)) + amount) by {
            rewrite(count(slot(pool)) == pool->capacity); simp();
        }
        step();
        fold(amount of slot(pool));
        have pool->capacity == count(slot(pool)) by simp;
    }
    execute(); simp();
}
void forward(struct pool* pool, int32 amount) {
    owns control(pool);
    requires 0 <= amount;
    requires defined(pool->capacity + amount);
    produces amount of slot(pool);
    ensures pool->capacity == old(pool->capacity) + amount;
    ensures count(slot(pool)) == old(count(slot(pool))) + amount;
    ensures pool->checked_out == old(pool->checked_out);
} by {
    open(control(pool)) {
        have count(slot(pool)) == pool->capacity by simp;
        have 0 <= count(slot(pool)) by simp;
        have 0 <= pool->capacity by {
            arithmetic() using { 0 <= count(slot(pool)); pool->capacity == count(slot(pool)); }
        }
        have defined(count(slot(pool)) + amount) by {
            rewrite(count(slot(pool)) == pool->capacity); simp();
        }
    }
    execute(); simp();
}
```

```expect
pass
```
