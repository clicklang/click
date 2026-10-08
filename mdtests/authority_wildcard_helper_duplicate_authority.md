# A wildcard helper cannot duplicate authority ownership

```c filename=wildcard_helper_duplicate_authority.c
void inspect(int32* pool, int32* member) {}
```

```click
authorized resource slot(pool: int32*, member: int32*) {}
verifying "wildcard_helper_duplicate_authority.c";
void inspect(int32* pool, int32* member) {
    owns authority(slot(pool, _));
    owns authority(slot(pool, _));
    owns slot(pool, member);
} by { execute(); simp(); }
```

```expect
fail: duplicate resource fact `owns authority(slot(pool, _))`
```
