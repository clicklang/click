# Named consumption requires a checked death

A consumed contract binder cannot silently drop its named occurrence.

```c filename=named_retirement.c
void retire(int32* pool) {}
```

```click resource_semantics=authority
authorized resource ticket(pool: int32*) { field serial: int32; }
verifying "named_retirement.c";
void retire(int32* pool) {
    owns authority(ticket(pool));
    consumes left: ticket(pool);
} by { execute(); simp(); }
```

```expect
fail: Requires a checked death for every consumed named member
```
