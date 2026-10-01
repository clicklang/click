# Arbitrary entry totals require a checked count bound before creation

```c filename=wildcard_create_missing_bound.c
void issue(int32* pool, int32* member) {}
```

```click resource_semantics=authority
resource slot(pool: int32*, member: int32*) {}
verifying "wildcard_create_missing_bound.c";
void issue(int32* pool, int32* member) {
    owns authority(slot(pool, _));
    produces slot(pool, member);
} by {
    fold(slot(pool, member));
    execute(); simp();
}
```

```expect
fail: Requires defined(count(slot(pool, _)) + 1)
```
