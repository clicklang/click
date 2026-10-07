# Creation must return the promised concrete member

```c filename=wildcard_create_wrong_member.c
void issue(int32* pool, int32* member) {}
```

```click resource_semantics=authority
authorized resource slot(pool: int32*, member: int32*) {}
verifying "wildcard_create_wrong_member.c";
void issue(int32* pool, int32* member) {
    owns authority(slot(pool, _));
    requires defined(count(slot(pool, _)) + 1);
    produces slot(pool, member);
} by {
    fold(slot(pool, pool));
    execute(); simp();
}
```

```expect
fail: slot
```
