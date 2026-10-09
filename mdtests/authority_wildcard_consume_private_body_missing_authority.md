# A memory-bearing member alone cannot authorize a consuming helper call

```c filename=wildcard_consume_private_body_missing_authority.c
void release(int32* pool, int32* p) { p[0] = 0; }
void caller(int32* pool, int32* p) { release(pool, p); }
```

```click
authorized resource slot(pool: int32*, p: int32*) { owns p[0..1]; }
verifying "wildcard_consume_private_body_missing_authority.c";
void release(int32* pool, int32* p) {
    owns authority(slot(pool, _));
    consumes slot(pool, p);
    produces p[0..1];
    ensures p[0] == 0;
    ensures count(slot(pool, _)) == old(count(slot(pool, _))) - 1;
} by { unfold(slot(pool, p)); execute(); simp(); }
void caller(int32* pool, int32* p) {
    consumes slot(pool, p);
    produces p[0..1];
} by { execute(); simp(); }
```

```expect
fail: Requires owns authority
```
