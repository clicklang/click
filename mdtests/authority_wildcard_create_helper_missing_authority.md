# Creating a member requires authority

```c filename=wildcard_create_missing_authority.c
void issue(int32* pool, int32* member) {}
```

```click
authorized resource slot(pool: int32*, member: int32*) {}
verifying "wildcard_create_missing_authority.c";
void issue(int32* pool, int32* member) {
    produces slot(pool, member);
} by {
    fold(slot(pool, member));
    execute(); simp();
}
```

```expect
fail: Requires live base storage
```
