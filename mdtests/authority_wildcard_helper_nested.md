# Nested helpers preserve a three-argument member and wildcard total

```c filename=wildcard_helper_nested.c
void inspect(int32* pool, int32* member, int32 tag) {}
void forward(int32* pool, int32* member, int32 tag) {
    inspect(pool, member, tag);
}
void lifecycle() {
    int32 pool = 0;
    int32 first = 0;
    int32 second = 0;
    forward(&pool, &first, 10);
}
```

```click
authorized resource slot(pool: int32*, member: int32*, tag: int32) {}
verifying "wildcard_helper_nested.c";
void inspect(int32* pool, int32* member, int32 tag) {
    owns authority(slot(pool, _, _));
    owns slot(pool, member, tag);
    ensures count(slot(pool, _, _)) == old(count(slot(pool, _, _)));
} by { execute(); simp(); }
void forward(int32* pool, int32* member, int32 tag) {
    owns authority(slot(pool, _, _));
    owns slot(pool, member, tag);
    ensures count(slot(pool, _, _)) == old(count(slot(pool, _, _)));
} by { execute(); simp(); }
void lifecycle() { ensures 1 == 1; } by {
    step(); step(); step(); step(); step(); step();
    fold(authority(slot(&pool, _, _)));
    fold(slot(&pool, &first, 10));
    fold(slot(&pool, &second, 20));
    step();
    have count(slot(&pool, _, _)) == 2;
    unfold(slot(&pool, &first, 10));
    unfold(slot(&pool, &second, 20));
    unfold(authority(slot(&pool, _, _)));
    execute(); simp();
}
```

```expect
pass
```
