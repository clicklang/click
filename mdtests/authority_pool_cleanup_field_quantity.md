# A field-valued cleanup quantity consumes a concrete owned batch

Cleanup is the unchanged bounded-pool implementation. The caller owns two
concrete slots while the helper requests its field-valued entry capacity.
Checked equality must let those spellings describe the same batch without
creating member rights.

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

```c filename=cleanup_helper.c
struct pool { int32 checked_out; int32 capacity; };
void pool_destroy(struct pool* pool);
void fixed(struct pool* pool) { pool_destroy(pool); }
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
verifying "cleanup_helper.c";
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
void fixed(struct pool* pool) {
    consumes pool_control(pool);
    consumes 2 of pool_slot(pool);
    requires pool->checked_out == 0;
    requires pool->capacity == 2;
    produces *pool;
    ensures pool->checked_out == 0;
    ensures pool->capacity == 0;
    ensures count(pool_slot(pool)) == 0;
    ensures count(pool_object(pool, _)) == 0;
    ensures valid_pool(pool);
} by {
    unfold(pool_control(pool));
    have pool->capacity == count(pool_slot(pool)) by simp;
    have count(pool_object(pool, _)) == 0 by simp;
    fold(pool_control(pool));
    execute(); unfold(valid_pool); simp();
}

```

```expect
pass
```
