# A consumes clause must be backed by an actual checked death

```c filename=wildcard_consume_missing_event.c
void release(int32* pool, int32* member) {}
```

```click resource_semantics=authority
resource slot(pool: int32*, member: int32*) {}
verifying "wildcard_consume_missing_event.c";
void release(int32* pool, int32* member) {
    owns authority(slot(pool, _));
    consumes slot(pool, member);
} by { execute(); simp(); }
```

```expect
fail: Requires consumes slot(pool, member)
```
