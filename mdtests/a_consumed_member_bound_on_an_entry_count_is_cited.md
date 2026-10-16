# A consumed member's bound on an entry count is cited

Consuming `pool_slot(pool)` makes the kernel record that the slot count at
function entry is at least one. That count is an opaque entry symbol, which
`auto` could not cite before it had a spelling; it is now spelled
`old(count(pool_slot(pool)))`, so under `arithmetic "integer";` the bound
carries to Integer and the checkout's definedness and ledger facts follow by
`auto()`.

```c filename=a_consumed_member_bound_on_an_entry_count_is_cited.c
struct pool {
    int checked_out;
    int capacity;
};

struct object {
    int value;
};

void pool_checkout(struct pool *pool, struct object *object) {
    pool->checked_out = pool->checked_out + 1;
}
```

```click
arithmetic "integer";

verifying "a_consumed_member_bound_on_an_entry_count_is_cited.c";
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
void pool_checkout(struct pool* pool, struct object* object) {
    owns pool_control(pool);
    consumes pool_slot(pool);
    consumes *object;
    produces pool_object(pool, object);
    ensures pool->checked_out == old(pool->checked_out) + 1;
} by {
    open(pool_control(pool)) {
        have count(pool_slot(pool)) >= 1 by auto();
        have defined(count(pool_object(pool, _)) + 1) by auto();
        have defined(pool->checked_out + 1) by auto();
        unfold(pool_slot(pool));
        step();
        fold(pool_object(pool, object));
        have defined(old(pool->checked_out) + 1) by auto();
        have to_integer(pool->checked_out) == to_integer(count(pool_object(pool, _))) by auto();
        have to_integer(pool->capacity)
            == to_integer(pool->checked_out) + to_integer(count(pool_slot(pool))) by auto();
    }
    execute();
}
```

```expect
pass
```
