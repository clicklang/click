# A member-only helper updates a private body without population authority

The caller keeps authority and another member. Updating private memory is
not a membership change.

```c filename=wildcard_private_body_helper.c
int32 update(int32* pool, int32* p) { p[0] = 7; return 7; }
int32 lifecycle() {
    int32 pool = 0;
    int32* p = malloc(8);
    if (p == 0) return 0;
    p[0] = 1;
    p[1] = 2;
    update(&pool, p);
    int32 result = p[0] + p[1];
    free(p);
    return result;
}
```

```click resource_semantics=authority
resource slot(pool: int32*, p: int32*) { owns p[0..1]; }
verifying "wildcard_private_body_helper.c";
int32 update(int32* pool, int32* p) {
    owns slot(pool, p);
    ensures result == 7;
    ensures p[0] == 7;
} by { open(slot(pool, p)) { step(); } execute(); simp(); }
int32 lifecycle() { ensures result == 0 or result == 9; } by {
    step(); step(); step(); step();
    branch { then { execute(); simp(); } else {} }
    step(); step();
    fold(authority(slot(&pool, _)));
    fold(slot(&pool, p));
    fold(slot(&pool, p + 1));
    step();
    have count(slot(&pool, _)) == 2 by simp;
    open(slot(&pool, p)) {
        open(slot(&pool, p + 1)) { step(); step(); }
    }
    unfold(slot(&pool, p));
    unfold(slot(&pool, p + 1));
    unfold(authority(slot(&pool, _)));
    execute(); simp();
}
```

```expect
pass
```
