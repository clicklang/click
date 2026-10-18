# An Integer entry count premise folds a grown count

A count premise stated at entry with `to_integer` serves a `fold` as its
machine form does. Here the pool's slot count is zero at entry and
`fold(capacity of pool_slot(pool))` adds `capacity` slots. Folding
`pool_control` requires the Integer ledger fact
`to_integer(pool->capacity) == to_integer(pool->checked_out) + to_integer(count(pool_slot(pool)))`
over the grown count `entry + capacity`. The Integer premise
`to_integer(entry) == 0` also establishes the native `entry == 0`, so the
fold's check decides the ledger fact without a search.

```c filename=an_integer_entry_count_premise_folds_a_grown_count.c
struct pool {
    int checked_out;
    int capacity;
};

void pool_init(struct pool *pool, int capacity) {
    pool->checked_out = 0;
    pool->capacity = capacity;
}
```

```click
verifying "an_integer_entry_count_premise_folds_a_grown_count.c";
authorized resource pool_slot(pool: struct pool*) {}
resource pool_storage(pool: struct pool*) {
    owns *pool;
    owns authority(pool_slot(pool));
}
resource pool_control(pool: struct pool*) {
    owns *pool;
    owns authority(pool_slot(pool));
    fact to_integer(pool->capacity)
        == to_integer(pool->checked_out) + to_integer(count(pool_slot(pool)));
}
void pool_init(struct pool* pool, int32 capacity) {
    consumes pool_storage(pool);
    requires 0 <= capacity;
    requires to_integer(count(pool_slot(pool))) == 0;
    produces pool_control(pool);
    produces capacity of pool_slot(pool);
} by {
    unfold(pool_storage(pool));
    step(); step();
    fold(capacity of pool_slot(pool));
    fold(pool_control(pool));
    execute();
}
```

```expect
pass
```
