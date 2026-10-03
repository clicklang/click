# A helper consumes a member and returns its private memory

The helper's entry population total is arbitrary. Its concrete member becomes
raw owned memory, while the caller keeps its other member and allocation.

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

```click resource_semantics=authority
resource slot(pool: int32*, p: int32*) { owns p[0..1]; }
verifying "wildcard_consume_private_body.c";
void release(int32* pool, int32* p) {
    owns authority(slot(pool, _));
    consumes slot(pool, p);
    produces p[0..1];
    ensures p[0] == 0;
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
    fold(slot(&pool, p));
    fold(slot(&pool, p + 1));
    step();
    have count(slot(&pool, _)) == 1 by simp;
    open(slot(&pool, p + 1)) { step(); step(); }
    unfold(slot(&pool, p + 1));
    unfold(authority(slot(&pool, _)));
    execute(); simp();
}
```

```expect
pass
```
