# An exact member's count is spelled from its entry count

Without the empty-population law, the call's requirement on an exact member's
count is left open, and the refusal spells that count `old(count(R(a, k)))`
rather than a report-local `<unnamed A>`.

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
    step();
    step_until(function.exit);
}
```

```expect
fail: old(count(item(pool, object))) >= 0 implies old(count(item(pool, object))) == 0
```
