# predicate preconditions preserve captured authority counts

A precondition reaches a count through a second named predicate. Unfolding both
must use the captured authority model, so a positive population implies a
positive unchanged C counter. The explicit rewrite records the equality used.

```c filename=inspect.c
struct pool { int32 checked_out; };
void inspect(struct pool* pool) {}
```

```click resource_semantics=authority
abstract resource available(object: int32);
resource pool_object(pool: struct pool*, object: int32) {
    owns available(object);
}
predicate valid_pool(pool: struct pool*) {
    pool->checked_out == count(pool_object(pool, _))
}
predicate wrapped_valid_pool(pool: struct pool*) {
    valid_pool(pool)
}
verifying "inspect.c";
void inspect(struct pool* pool) {
    owns pool->checked_out;
    owns authority(pool_object(pool, _));
    requires wrapped_valid_pool(pool);
    requires 0 < count(pool_object(pool, _));
    ensures 0 < pool->checked_out;
} by {
    unfold(wrapped_valid_pool);
    unfold(valid_pool);
    have 0 < pool->checked_out by {
        rewrite(pool->checked_out == count(pool_object(pool, _)));
        assumption();
    }
    execute();
    simp();
}
```

```expect
pass
```
