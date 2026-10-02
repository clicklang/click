# Authority alone does not permit a memory read in a quantity

```c filename=quantity.c
struct pool { int32 capacity; };
void inspect(struct pool* pool) {}
```

```click resource_semantics=authority
resource slot(pool: struct pool*) {}
resource control(pool: struct pool*) {
    owns object(pool);
    owns authority(slot(pool));
    fact pool->capacity == count(slot(pool));
}
verifying "quantity.c";
void inspect(struct pool* pool) {
    owns authority(slot(pool));
    owns pool->capacity of slot(pool);
} by {
    execute(); simp();
}
```

```expect
fail: declared resource quantity must evaluate to int32
```
