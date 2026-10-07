# Consumption must select the member received on entry

```c filename=wildcard_consume_wrong_member.c
void release(int32* pool, int32* member) {}
```

```click resource_semantics=authority
authorized resource slot(pool: int32*, member: int32*) {}
verifying "wildcard_consume_wrong_member.c";
void release(int32* pool, int32* member) {
    owns authority(slot(pool, _));
    consumes slot(pool, member);
} by { unfold(slot(pool, pool)); execute(); simp(); }
```

```expect
fail: Requires owns slot(p)
```
