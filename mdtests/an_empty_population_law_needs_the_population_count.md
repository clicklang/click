# The empty-population law needs its population's count

`population_member_count_zero` concludes an exact member's count is zero only
from an available `count(R(a, _)) == 0`.

```c filename=pool.c
struct pool { int checked_out; };
struct object { int value; };
void caller(struct pool* pool, struct object* object) {}
```

```click
authorized resource item(pool: struct pool*, p: struct object*) {}
resource control(pool: struct pool*) {
    owns *pool;
    owns authority(item(pool, _));
}
verifying "pool.c";
void caller(struct pool* pool, struct object* object) {
    owns control(pool);
} by {
    open(control(pool)) {
        apply(population_member_count_zero(count(item(pool, object))));
    }
    step_until(function.exit);
}
```

```expect
fail: listed premise `count(item(pool, _)) == 0` is not an available fact
```
