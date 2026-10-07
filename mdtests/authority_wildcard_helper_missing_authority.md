# A caller must supply a helper's authority

```c filename=wildcard_helper_missing_authority.c
void inspect(int32* pool, int32* member) {}
void caller(int32* pool, int32* member) { inspect(pool, member); }
```

```click resource_semantics=authority
authorized resource slot(pool: int32*, member: int32*) {}
verifying "wildcard_helper_missing_authority.c";
void inspect(int32* pool, int32* member) {
    owns authority(slot(pool, _));
    owns slot(pool, member);
} by { execute(); simp(); }
void caller(int32* pool, int32* member) {
    owns slot(pool, member);
} by { execute(); simp(); }
```

```expect
fail: Requires owns authority
```
