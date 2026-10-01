# Authority alone does not grant a slot's private memory

```c filename=wildcard_private_missing_member.c
void update(int32* pool, int32* p) { p[0] = 7; }
```

```click resource_semantics=authority
resource slot(pool: int32*, p: int32*) { owns p[0..1]; }
verifying "wildcard_private_missing_member.c";
void update(int32* pool, int32* p) {
    owns authority(slot(pool, _));
} by { open(slot(pool, p)) { step(); } execute(); simp(); }
```

```expect
fail: Requires owns slot(pool, p)
```
