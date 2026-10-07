# A caller cannot authorize consumption with a member alone

```c filename=wildcard_consume_missing_authority.c
void release(int32* pool, int32* member) {}
void caller(int32* pool, int32* member) { release(pool, member); }
```

```click resource_semantics=authority
authorized resource slot(pool: int32*, member: int32*) {}
verifying "wildcard_consume_missing_authority.c";
void release(int32* pool, int32* member) {
    owns authority(slot(pool, _));
    consumes slot(pool, member);
} by { unfold(slot(pool, member)); execute(); simp(); }
void caller(int32* pool, int32* member) {
    consumes slot(pool, member);
} by { execute(); simp(); }
```

```expect
fail: Requires owns authority
```
