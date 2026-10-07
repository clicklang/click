# Zero quantity helper transfer grants no member capability

```c filename=batch_helper.c
struct pool { int32 capacity; };
void preserve(struct pool* pool) {}
void forward(struct pool* pool) { preserve(pool); }
void nested(struct pool* pool) { forward(pool); }
```

```click resource_semantics=authority
authorized resource slot(pool: struct pool*) {}
resource control(pool: struct pool*) {
    owns object(pool);
    owns authority(slot(pool));
    fact pool->capacity == count(slot(pool));
}
verifying "batch_helper.c";
void preserve(struct pool* pool) {
    owns control(pool);
    owns pool->capacity of slot(pool);
    ensures pool->capacity == old(pool->capacity);
    ensures count(slot(pool)) == old(count(slot(pool)));
} by { execute(); simp(); }
void forward(struct pool* pool) {
    owns control(pool);
    owns 0 of slot(pool);
    requires pool->capacity == 0;
    ensures pool->capacity == old(pool->capacity);
    ensures count(slot(pool)) == old(count(slot(pool)));
} by { execute(); simp(); }
```

```expect
pass
```
