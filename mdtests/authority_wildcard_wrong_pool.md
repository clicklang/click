# The authority for one pool cannot authorize births in another.

```c filename=wildcard_lifecycle.c
void lifecycle() {
    int32 pool = 0;
    int32 first = 0;
    int32 second = 0;
}
```

```click resource_semantics=authority
authorized resource slot(pool: int32*, member: int32*) {}
verifying "wildcard_lifecycle.c";
void lifecycle() { ensures 1 == 1; } by {
    step(); step(); step(); step(); step(); step();
    fold(authority(slot(&pool, _)));
    have count(slot(&pool, _)) == 0 by simp;
    fold(slot(&first, &second));
    fold(slot(&pool, &second));
    have count(slot(&pool, _)) == 2 by simp;
    unfold(slot(&pool, &first));
    have count(slot(&pool, _)) == 1 by simp;
    unfold(slot(&pool, &second));
    have count(slot(&pool, _)) == 0 by simp;
    unfold(authority(slot(&pool, _)));
    execute(); simp();
}
```

```expect
fail: Requires owns authority(
```
