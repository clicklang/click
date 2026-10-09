# A named birth can be consumed without inventing an entry occurrence

```c filename=issue.c
void issue(int32* pool) {}
void nested(int32* pool) { issue(pool); }
int32 run() { int32 pool = 0; nested(&pool); return 0; }
```

```click
authorized resource ticket(pool: int32*) { field serial: int32; }
verifying "issue.c";
void issue(int32* pool) {
    owns authority(ticket(pool));
    requires defined(count(ticket(pool)) + 1);
    ensures count(ticket(pool)) == old(count(ticket(pool)));
} by { let member = fold(ticket(pool), { serial: 7 }); unfold(member); execute(); simp(); }
```

```expect
pass
```
