# A helper borrows a wildcard authority and one concrete member

The caller retains a second member. The helper returns both inputs and
preserves an arbitrary population total, rather than equating it to the
number of members it receives.

```c filename=wildcard_helper_borrow.c
void inspect(int32* pool, int32* member) {}
void lifecycle() {
    int32 pool = 0;
    int32 first = 0;
    int32 second = 0;
    inspect(&pool, &first);
}
```

```click resource_semantics=authority
authorized resource slot(pool: int32*, member: int32*) {}
verifying "wildcard_helper_borrow.c";
void inspect(int32* pool, int32* member) {
    owns authority(slot(pool, _));
    owns slot(pool, member);
    ensures count(slot(pool, _)) == old(count(slot(pool, _)));
} by {
    execute(); simp();
}
void lifecycle() { ensures 1 == 1; } by {
    step(); step(); step(); step(); step(); step();
    fold(authority(slot(&pool, _)));
    fold(slot(&pool, &first));
    fold(slot(&pool, &second));
    step();
    have count(slot(&pool, _)) == 2;
    unfold(slot(&pool, &first));
    unfold(slot(&pool, &second));
    unfold(authority(slot(&pool, _)));
    execute(); simp();
}
```

```expect
pass
```
