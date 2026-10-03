# Initialization packages two passed authorities into an ordinary control

```c filename=pool_init_control.c
struct pool { int32 checked_out; int32 capacity; };
struct payload { int32 value; };
void initialize(struct pool* pool, int32 amount) {
    pool->checked_out = 0;
    pool->capacity = amount;
}
void forward(struct pool* pool) { initialize(pool, 2); }
```

```click resource_semantics=authority
resource slot(pool: struct pool*) {}
resource item(pool: struct pool*, p: struct payload*) { owns object(p); }
resource storage(pool: struct pool*) {
    owns object(pool);
    owns authority(slot(pool));
    owns authority(item(pool, _));
}
resource control(pool: struct pool*) {
    owns object(pool);
    owns authority(slot(pool));
    owns authority(item(pool, _));
    fact 0 <= pool->checked_out;
    fact pool->checked_out == count(item(pool, _));
    fact pool->capacity == pool->checked_out + count(slot(pool));
}
predicate valid_pool(pool: struct pool*) {
    0 <= pool->checked_out and
    pool->checked_out == count(item(pool, _)) and
    pool->capacity == pool->checked_out + count(slot(pool))
}
verifying "pool_init_control.c";
void initialize(struct pool* pool, int32 amount) {
    consumes storage(pool);
    requires 0 <= amount;
    requires count(slot(pool)) == 0;
    requires count(item(pool, _)) == 0;
    produces control(pool);
    produces amount of slot(pool);
    ensures pool->capacity == amount;
    ensures valid_pool(pool);
} by {
    unfold(storage(pool));
    step(); step();
    fold(amount of slot(pool));
    fold(control(pool));
    execute(); unfold(valid_pool); simp();
}
void forward(struct pool* pool) {
    consumes storage(pool);
    requires count(slot(pool)) == 0;
    requires count(item(pool, _)) == 0;
    produces control(pool);
    produces 2 of slot(pool);
    ensures pool->capacity == 2;
    ensures valid_pool(pool);
    ensures count(slot(pool)) == 2;
} by { execute(); unfold(valid_pool); simp(); }
```

```expect
pass
```
