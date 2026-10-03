# Consumption cannot import a member of a different population

```c filename=wildcard_consume_wrong_pool.c
void release(int32* pool, int32* other, int32* member) {}
```

```click resource_semantics=authority
resource slot(pool: int32*, member: int32*) {}
verifying "wildcard_consume_wrong_pool.c";
void release(int32* pool, int32* other, int32* member) {
    owns authority(slot(pool, _));
    consumes slot(other, member);
} by { unfold(slot(other, member)); execute(); simp(); }
```

```expect
fail: Requires live base storage
```
