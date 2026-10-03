# A helper consumes one concrete member under wildcard authority

The helper receives an arbitrary population total, not just its one member.
The caller retains two members and proves the count falls from three to two.

```c filename=wildcard_consume_helper.c
void release(int32* pool, int32* member) {}
void lifecycle() {
    int32 pool = 0;
    int32 first = 0;
    int32 second = 0;
    int32 third = 0;
    release(&pool, &third);
}
```

```click resource_semantics=authority
resource slot(pool: int32*, member: int32*) {}
verifying "wildcard_consume_helper.c";
void release(int32* pool, int32* member) {
    owns authority(slot(pool, _));
    consumes slot(pool, member);
    ensures count(slot(pool, _)) == old(count(slot(pool, _))) - 1;
} by {
    unfold(slot(pool, member));
    execute(); simp();
}
void lifecycle() { ensures 1 == 1; } by {
    step(); step(); step(); step(); step(); step(); step(); step();
    fold(authority(slot(&pool, _)));
    fold(slot(&pool, &first));
    fold(slot(&pool, &second));
    fold(slot(&pool, &third));
    step();
    have count(slot(&pool, _)) == 2 by simp;
    unfold(slot(&pool, &first));
    unfold(slot(&pool, &second));
    unfold(authority(slot(&pool, _)));
    execute(); simp();
}
```

```expect
pass
```
