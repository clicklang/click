# Nested helpers consume an exact three-argument member

```c filename=wildcard_consume_helper_nested.c
void release(int32* pool, int32* member, int32 tag) {}
void forward(int32* pool, int32* member, int32 tag) {
    release(pool, member, tag);
}
void lifecycle() {
    int32 pool = 0;
    int32 first = 0;
    int32 second = 0;
    forward(&pool, &first, 10);
}
```

```click resource_semantics=authority
authorized resource slot(pool: int32*, member: int32*, tag: int32) {}
verifying "wildcard_consume_helper_nested.c";
void release(int32* pool, int32* member, int32 tag) {
    owns authority(slot(pool, _, _));
    consumes slot(pool, member, tag);
    ensures count(slot(pool, _, _)) == old(count(slot(pool, _, _))) - 1;
} by { unfold(slot(pool, member, tag)); execute(); simp(); }
void forward(int32* pool, int32* member, int32 tag) {
    owns authority(slot(pool, _, _));
    consumes slot(pool, member, tag);
    ensures count(slot(pool, _, _)) == old(count(slot(pool, _, _))) - 1;
} by { execute(); simp(); }
void lifecycle() { ensures 1 == 1; } by {
    step(); step(); step(); step(); step(); step();
    fold(authority(slot(&pool, _, _)));
    fold(slot(&pool, &first, 10));
    fold(slot(&pool, &second, 20));
    step();
    have count(slot(&pool, _, _)) == 1 by simp;
    unfold(slot(&pool, &second, 20));
    unfold(authority(slot(&pool, _, _)));
    execute(); simp();
}
```

```expect
pass
```
