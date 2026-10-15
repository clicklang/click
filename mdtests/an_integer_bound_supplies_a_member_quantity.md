# an Integer bound supplies a member quantity

A built-in check reads machine facts, and an Integer premise about
`to_integer(capacity)` files the native fact it is equivalent to. Here
`0 <= to_integer(capacity)` gives `fold(capacity of pool_slot(pool))` the
nonnegative quantity it needs, and `to_integer(count(pool_slot(pool))) == 0`
gives the count update its exact base, so `count(pool_slot(pool))` after the
fold is defined.

```c filename=an_integer_bound_supplies_a_member_quantity.c
struct pool {
    int checked_out;
    int capacity;
};

void pool_init(struct pool* pool, int capacity) {
    pool->checked_out = 0;
    pool->capacity = capacity;
}
```

```click
verifying "an_integer_bound_supplies_a_member_quantity.c";

authorized resource pool_slot(pool: struct pool*) {}
resource pool_storage(pool: struct pool*) {
    owns *pool;
    owns authority(pool_slot(pool));
}
resource pool_control(pool: struct pool*) {
    owns *pool;
    owns authority(pool_slot(pool));
    fact pool->capacity == pool->checked_out + count(pool_slot(pool));
}

void pool_init(struct pool* pool, int32 capacity) {
    consumes pool_storage(pool);
    requires 0 <= to_integer(capacity);
    requires to_integer(count(pool_slot(pool))) == 0;
    produces pool_control(pool);
    produces capacity of pool_slot(pool);
    ensures to_integer(pool->capacity) == to_integer(capacity);
} by {
    unfold(pool_storage(pool));
    step(); step();
    fold(capacity of pool_slot(pool));
    fold(pool_control(pool));
    execute(); simp();
}
```

```expect
pass
```
