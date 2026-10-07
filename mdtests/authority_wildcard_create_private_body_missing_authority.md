# Memory alone cannot authorize a helper to create membership

```c filename=wildcard_create_private_body_missing_authority.c
void issue(int32* pool, int32* p) { p[0] = 7; }
void caller(int32* pool, int32* p) { issue(pool, p); }
```

```click resource_semantics=authority
authorized resource slot(pool: int32*, p: int32*) { owns p[0..1]; }
verifying "wildcard_create_private_body_missing_authority.c";
void issue(int32* pool, int32* p) {
    owns authority(slot(pool, _));
    consumes p[0..1];
    requires defined(count(slot(pool, _)) + 1);
    produces slot(pool, p);
} by { step(); fold(slot(pool, p)); execute(); simp(); }
void caller(int32* pool, int32* p) {
    consumes p[0..1];
    produces slot(pool, p);
} by { execute(); simp(); }
```

```expect
fail: Requires owns authority
```
