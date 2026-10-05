# An external authority contract cannot spend a named occurrence

```c filename=helper.c
extern void preserve(int32* pool);
int32 run() { int32 pool = 0; preserve(&pool); return 0; }
```

```click resource_semantics=authority
resource ticket(pool: int32*) { field serial: int32; }
verifying "helper.c";
extern void preserve(int32* pool) {
    owns authority(ticket(pool));
    consumes member: ticket(pool);
    ensures count(ticket(pool)) == old(count(ticket(pool))) - 1;
}
int32 run() { ensures result == 0; } by {
    step(); step();
    fold(authority(ticket(&pool)));
    let first = fold(ticket(&pool), { serial: 1 });
    step(preserve(&pool), { member: first });
    have first.serial == 1 by simp;
    have count(ticket(&pool)) == 1 by simp;
    unfold(first);
    unfold(authority(ticket(&pool)));
    execute(); simp();
}
```

```expect
fail: C calls are not yet supported by authority resource semantics
```
