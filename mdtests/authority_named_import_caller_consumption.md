# Checked named consumption reaches callers and nested helper boundaries

```c filename=helper.c
void retire(int32* pool) {}
void nested(int32* pool) { retire(pool); }
int32 run() { int32 pool = 0; nested(&pool); return 0; }
```

```click resource_semantics=authority
authorized resource ticket(pool: int32*) { field serial: int32; }
verifying "helper.c";
void retire(int32* pool) {
    owns authority(ticket(pool));
    consumes member: ticket(pool);
    ensures count(ticket(pool)) == old(count(ticket(pool))) - 1;
} by { unfold(member); execute(); simp(); }
void nested(int32* pool) {
    owns authority(ticket(pool));
    consumes member: ticket(pool);
    ensures count(ticket(pool)) == old(count(ticket(pool))) - 1;
} by { step(retire(pool), { member: member }); execute(); simp(); }
int32 run() { ensures result == 0; } by {
    step(); step();
    fold(authority(ticket(&pool)));
    let first = fold(ticket(&pool), { serial: 1 });
    let second = fold(ticket(&pool), { serial: 2 });
    step(nested(&pool), { member: first });
    have second.serial == 2;
    have count(ticket(&pool)) == 1;
    unfold(second); unfold(authority(ticket(&pool)));
    execute(); simp();
}
```

```expect
pass
```
