# A helper creates one member in an existing wildcard population

The caller retains two other members. Helper entry has an arbitrary total,
and the produced member increases it by one.

```c filename=wildcard_create_helper.c
void issue(int32* pool, int32* member) {}
void lifecycle() {
    int32 pool = 0;
    int32 first = 0;
    int32 second = 0;
    int32 third = 0;
    issue(&pool, &third);
}
```

```click resource_semantics=authority
authorized resource slot(pool: int32*, member: int32*) {}
verifying "wildcard_create_helper.c";
void issue(int32* pool, int32* member) {
    owns authority(slot(pool, _));
    requires defined(count(slot(pool, _)) + 1);
    produces slot(pool, member);
    ensures count(slot(pool, _)) == old(count(slot(pool, _))) + 1;
} by {
    fold(slot(pool, member));
    execute(); simp();
}
void lifecycle() { ensures 1 == 1; } by {
    step(); step(); step(); step(); step(); step(); step(); step();
    fold(authority(slot(&pool, _)));
    fold(slot(&pool, &first));
    fold(slot(&pool, &second));
    step();
    have count(slot(&pool, _)) == 3 by simp;
    unfold(slot(&pool, &first));
    unfold(slot(&pool, &second));
    unfold(slot(&pool, &third));
    unfold(authority(slot(&pool, _)));
    execute(); simp();
}
```

```expect
pass
```
