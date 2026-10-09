# A named member alone does not permit a global count observation

```c filename=helper.c
void observe(int32* pool) {}
```

```click
authorized resource ticket(pool: int32*) { field serial: int32; }
verifying "helper.c";
void observe(int32* pool) {
    owns member: ticket(pool);
    ensures count(ticket(pool)) >= 1;
} by { execute(); simp(); }
```

```expect
fail: count(...) requires owning authority
```
