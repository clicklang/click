# Every consumed named input requires a checked death

A consumed contract binder cannot silently drop its named occurrence.

```c filename=named_retirement.c
void retire(int32* pool) {}
```

```click
authorized resource ticket(pool: int32*) { field serial: int32; }
verifying "named_retirement.c";
void retire(int32* pool) {
    owns authority(ticket(pool));
    consumes left: ticket(pool);
    consumes right: ticket(pool);
} by { unfold(left); execute(); simp(); }
```

```expect
fail: Requires a checked death for every consumed named member
```
