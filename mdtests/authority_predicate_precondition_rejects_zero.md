# predicate preconditions cannot silently reset authority counts

The predicate equates the unchanged C counter to a positive authenticated
population. Capturing a legacy empty model would incorrectly unfold this
predicate to a zero counter. The false zero postcondition must be refused.

```c filename=inspect.c
struct pool { int32 checked_out; };
void inspect(struct pool* pool) {}
```

```click resource_semantics=authority
abstract resource available(object: int32);
authorized resource pool_object(pool: struct pool*, object: int32) {
    owns available(object);
}
predicate valid_pool(pool: struct pool*) {
    pool->checked_out == count(pool_object(pool, _))
}
verifying "inspect.c";
void inspect(struct pool* pool) {
    owns pool->checked_out;
    owns authority(pool_object(pool, _));
    requires valid_pool(pool);
    requires 0 < count(pool_object(pool, _));
    ensures pool->checked_out == 0;
} by {
    unfold(valid_pool);
    execute();
    simp();
}
```

```expect
fail: unclosed goal
```
