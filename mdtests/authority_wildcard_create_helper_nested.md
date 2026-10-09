# A nested helper creates a three-argument member

```c filename=wildcard_create_nested.c
void issue(int32* pool, int32* member, int32 tag) {}
void forward(int32* pool, int32* member, int32 tag) { issue(pool, member, tag); }
void lifecycle() {
    int32 pool = 0;
    int32 first = 0;
    int32 second = 0;
    int32 third = 0;
    forward(&pool, &third, 30);
}
```

```click
authorized resource slot(pool: int32*, member: int32*, tag: int32) {}
verifying "wildcard_create_nested.c";
void issue(int32* pool, int32* member, int32 tag) {
    owns authority(slot(pool, _, _));
    requires defined(count(slot(pool, _, _)) + 1);
    produces slot(pool, member, tag);
    ensures count(slot(pool, _, _)) == old(count(slot(pool, _, _))) + 1;
} by { fold(slot(pool, member, tag)); execute(); simp(); }
void forward(int32* pool, int32* member, int32 tag) {
    owns authority(slot(pool, _, _));
    requires defined(count(slot(pool, _, _)) + 1);
    produces slot(pool, member, tag);
    ensures count(slot(pool, _, _)) == old(count(slot(pool, _, _))) + 1;
} by { execute(); simp(); }
void lifecycle() { ensures 1 == 1; } by {
    step(); step(); step(); step(); step(); step(); step(); step();
    fold(authority(slot(&pool, _, _)));
    fold(slot(&pool, &first, 10));
    fold(slot(&pool, &second, 20));
    step();
    have count(slot(&pool, _, _)) == 3;
    unfold(slot(&pool, &first, 10));
    unfold(slot(&pool, &second, 20));
    unfold(slot(&pool, &third, 30));
    unfold(authority(slot(&pool, _, _)));
    execute(); simp();
}
```

```expect
pass
```
