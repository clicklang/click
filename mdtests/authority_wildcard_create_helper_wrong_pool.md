# Authority for one pool cannot create a member in another

```c filename=wildcard_create_wrong_pool.c
void issue(int32* pool, int32* other, int32* member) {}
```

```click resource_semantics=authority
authorized resource slot(pool: int32*, member: int32*) {}
verifying "wildcard_create_wrong_pool.c";
void issue(int32* pool, int32* other, int32* member) {
    owns authority(slot(pool, _));
    requires defined(count(slot(pool, _)) + 1);
    produces slot(other, member);
} by {
    fold(slot(other, member));
    execute(); simp();
}
```

```expect
fail: Requires live base storage
```
