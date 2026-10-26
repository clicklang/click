# An empty population counts no member

The count of an exact member is its own term; it never folds to `0` because
the facts prove its population empty. `population_member_count_zero` derives
`count(R(a, k)) == 0` from an available `count(R(a, _)) == 0`.

```c filename=pool.c
struct pool { int checked_out; };
struct object { int value; };
void need_absent(struct pool* pool, struct object* object) {}
void caller(struct pool* pool, struct object* object) { need_absent(pool, object); }
```

```click
authorized resource item(pool: struct pool*, p: struct object*) {}
resource control(pool: struct pool*) {
    owns *pool;
    owns authority(item(pool, _));
}
verifying "pool.c";
void need_absent(struct pool* pool, struct object* object) {
    owns control(pool);
    requires count(item(pool, object)) == 0;
}
void caller(struct pool* pool, struct object* object) {
    owns control(pool);
    requires count(item(pool, _)) == 0;
} by {
    open(control(pool)) {
        apply(population_member_count_zero(count(item(pool, object))));
    }
    step();
    step_until(function.exit);
}
```

```expect
pass
```
