# An Integer count equality retires its authority

Under `arithmetic "integer";` the pool's ledger fact and the proof's
`have count(pool_slot(pool)) == 0` are Integer comparisons. After the
capacity's slots are consumed the count is the word `entry - capacity`,
so the `have` establishes `to_integer(entry) - to_integer(capacity) == 0`.
Retiring the slot authority is a built-in check of the machine fact
`count == 0`. An Integer equality over `+`, `-` and `*` of 32-bit values
also files the equality of the wrapped words, which here is
`entry - capacity == 0`, so the authority retires. Only this direction
holds: equal words do not make equal Integers.

```c filename=an_integer_count_equality_retires_its_authority.c
struct pool {
    int checked_out;
    int capacity;
};

void pool_destroy(struct pool *pool) {
    pool->capacity = 0;
}
```

```click
arithmetic "integer";

verifying "an_integer_count_equality_retires_its_authority.c";
authorized resource pool_slot(pool: struct pool*) {}
resource pool_control(pool: struct pool*) {
    owns *pool;
    owns authority(pool_slot(pool));
    fact pool->capacity == pool->checked_out + count(pool_slot(pool));
}
void pool_destroy(struct pool* pool) {
    consumes pool_control(pool);
    consumes pool->capacity of pool_slot(pool);
    requires pool->checked_out == 0;
    produces *pool;
    ensures pool->capacity == 0;
} by {
    unfold(pool_control(pool));
    unfold(pool->capacity of pool_slot(pool));
    have count(pool_slot(pool)) == 0 by auto();
    step();
    unfold(authority(pool_slot(pool)));
    execute();
}
```

```expect
pass
```
