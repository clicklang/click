# An unrelated member may be framed beside a pool authority

```c filename=wildcard_helper_wrong_pool.c
void inspect(int32* pool, int32* other, int32* member) {}
```

```click resource_semantics=authority
resource slot(pool: int32*, member: int32*) {}
verifying "wildcard_helper_wrong_pool.c";
void inspect(int32* pool, int32* other, int32* member) {
    owns authority(slot(pool, _));
    owns slot(other, member);
} by { execute(); simp(); }
```

```expect
pass
```
