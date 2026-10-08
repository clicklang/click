# A member from another pool cannot bound this authority's count

The helper owns one member, but its anchor belongs to another population.
Importing the checked member bounds must preserve that scope.

```c filename=wildcard_count_bound_other_pool.c
void probe(int32* pool, int32* other, int32 object) {}
```

```click
authorized resource slot(pool: int32*, object: int32) {}
verifying "wildcard_count_bound_other_pool.c";
void probe(int32* pool, int32* other, int32 object) {
    requires pool != other;
    owns authority(slot(pool, _));
    owns slot(other, object);
    ensures 1 <= count(slot(pool, _));
} by {
    execute();
    simp();
}
```

```expect
fail: unclosed goal
```
