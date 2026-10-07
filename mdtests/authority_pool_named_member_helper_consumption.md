# A helper consumes a named pool member under its authority

The helper receives one identified member and the authority for its pool.
Consuming the member returns its private storage and reduces the population by
one, while preserving the same arbitrary entry population for every other slot.

```c filename=authority_pool_named_member_helper_consumption.c
void remove_member(int32* pool, int32* cell) {
    *pool = *pool - 1;
    *cell = 0;
}
```

```click resource_semantics=authority
verifying "authority_pool_named_member_helper_consumption.c";
authorized resource slot(pool: int32*, cell: int32*) {
    field label: int32;
    owns cell[0..1];
}
void remove_member(int32* pool, int32* cell) {
    owns authority(slot(pool, _));
    owns pool[0..1];
    consumes member: slot(pool, cell);
    requires pool[0] > 0;
    requires pool[0] == count(slot(pool, _));
    produces cell[0..1];
    ensures pool[0] == count(slot(pool, _));
    ensures count(slot(pool, _)) == old(count(slot(pool, _))) - 1;
} by {
    unfold(member);
    execute();
    simp();
}
```

```expect
pass
```
