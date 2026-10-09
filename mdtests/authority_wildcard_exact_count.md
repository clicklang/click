# Exact member counts under a wildcard authority

The family total and exact member counts are different observations. A helper
consumes just its selected member, preserving the caller's neighboring member.

```c filename=wildcard_consume_private_body.c
void release(int32* pool, int32* p) { p[0] = 0; }
int32 lifecycle() {
    int32 pool = 0;
    int32* p = malloc(8);
    if (p == 0) return 0;
    p[0] = 1;
    p[1] = 2;
    release(&pool, p);
    int32 result = p[0] + p[1];
    free(p);
    return result;
}
```

```click
authorized resource slot(pool: int32*, p: int32*) { owns p[0..1]; }
verifying "wildcard_consume_private_body.c";
void release(int32* pool, int32* p) {
    owns authority(slot(pool, _));
    requires count(slot(pool, p)) == 1;
    consumes slot(pool, p);
    produces p[0..1];
    ensures p[0] == 0;
    ensures count(slot(pool, p)) == 0;
    ensures count(slot(pool, _)) == old(count(slot(pool, _))) - 1;
} by {
    unfold(slot(pool, p));
    execute(); simp();
}
int32 lifecycle() { ensures result == 0 or result == 2; } by {
    step(); step(); step(); step();
    branch then { execute(); simp(); } else {}
    step(); step();
    fold(authority(slot(&pool, _)));
    have count(slot(&pool, p)) == 0;
    fold(slot(&pool, p));
    have count(slot(&pool, p)) == 1;
    have count(slot(&pool, p + 1)) == 0;
    fold(slot(&pool, p + 1));
    have count(slot(&pool, p)) == 1;
    have count(slot(&pool, p + 1)) == 1;
    have count(slot(&pool, _)) == 2;
    step();
    have count(slot(&pool, _)) == 1;
    have count(slot(&pool, p)) == 0;
    have count(slot(&pool, p + 1)) == 1;
    open(slot(&pool, p + 1)) { step(); step(); }
    unfold(slot(&pool, p + 1));
    unfold(authority(slot(&pool, _)));
    execute(); simp();
}
```

```expect
pass
```
