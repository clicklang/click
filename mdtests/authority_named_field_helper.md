# A helper preserves an identified member and its proof fields

```c filename=helper.c
void preserve(int32* pool) {}
int32 run() { int32 pool = 0; preserve(&pool); return 0; }
```

```click resource_semantics=authority
authorized resource ticket(pool: int32*) { field serial: int32; }
verifying "helper.c";
void preserve(int32* pool) {
    owns member: ticket(pool);
    ensures member.serial == old(member.serial);
} by { execute(); simp(); }
int32 run() { ensures result == 0; } by {
    step(); step();
    fold(authority(ticket(&pool)));
    let first = fold(ticket(&pool), { serial: 1 });
    step(preserve(&pool), { member: first });
    have first.serial == 1;
    have count(ticket(&pool)) == 1;
    unfold(first);
    unfold(authority(ticket(&pool)));
    execute(); simp();
}
```

```expect
pass
```
