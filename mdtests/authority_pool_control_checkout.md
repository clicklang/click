# Pool control preserves both population invariants through checkout

```c filename=pool_control.c
struct pool { int32 checked_out; int32 capacity; };
struct payload { int32 value; };
void checkout(struct pool* pool, struct payload* p) {
    pool->checked_out = pool->checked_out + 1;
}
void forward(struct pool* pool, struct payload* p) { checkout(pool, p); }
void caller(struct pool* pool, struct payload* p) { forward(pool, p); }
```

```click resource_semantics=authority
authorized resource slot(pool: struct pool*) {}
authorized resource item(pool: struct pool*, p: struct payload*) { owns object(p); }
resource control(pool: struct pool*) {
    owns object(pool);
    owns authority(slot(pool));
    owns authority(item(pool, _));
    fact 0 <= pool->checked_out;
    fact pool->checked_out == count(item(pool, _));
    fact pool->capacity == pool->checked_out + count(slot(pool));
}
verifying "pool_control.c";
void checkout(struct pool* pool, struct payload* p) {
    owns control(pool);
    requires pool->checked_out < 2147483647;
    consumes slot(pool);
    consumes object(p);
    produces item(pool, p);
    ensures count(slot(pool)) == old(count(slot(pool))) - 1;
    ensures count(item(pool, _)) == old(count(item(pool, _))) + 1;
    ensures pool->checked_out == old(pool->checked_out) + 1;
    ensures pool->capacity == old(pool->capacity);
} by {
    open(control(pool)) {
        have 1 <= count(slot(pool)) by simp;
        apply(int32_move_one_from_right_to_left_preserves_sum(
            pool->capacity, pool->checked_out, count(slot(pool))
        )) using {
            0 <= pool->checked_out;
            1 <= count(slot(pool));
            pool->capacity == pool->checked_out + count(slot(pool));
        }
        unfold(slot(pool));
        step();
        fold(item(pool, p));
        have pool->capacity == pool->checked_out + count(slot(pool)) by simp;
    }
    execute(); simp();
}
void forward(struct pool* pool, struct payload* p) {
    owns control(pool);
    requires pool->checked_out < 2147483647;
    consumes slot(pool);
    consumes object(p);
    produces item(pool, p);
    ensures count(slot(pool)) == old(count(slot(pool))) - 1;
    ensures count(item(pool, _)) == old(count(item(pool, _))) + 1;
    ensures pool->checked_out == old(pool->checked_out) + 1;
    ensures pool->capacity == old(pool->capacity);
} by { execute(); simp(); }
void caller(struct pool* pool, struct payload* p) {
    owns control(pool);
    requires pool->checked_out < 2147483647;
    owns slot(pool);
    consumes slot(pool);
    consumes object(p);
    produces item(pool, p);
    ensures count(slot(pool)) == old(count(slot(pool))) - 1;
    ensures count(item(pool, _)) == old(count(item(pool, _))) + 1;
    ensures pool->checked_out == old(pool->checked_out) + 1;
    ensures pool->capacity == old(pool->capacity);
} by { execute(); simp(); }
```

```expect
pass
```
