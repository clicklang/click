# An imported field schema gives no authority over another anchor

```c filename=helper.c
void preserve(int32* pool) {}
int32 run() { int32 pool = 0; preserve(&pool); return 0; }
```

```click
authorized resource ticket(pool: int32*) { field serial: int32; }
verifying "helper.c";
void preserve(int32* pool) {
    owns authority(ticket(pool));
    owns member: ticket(pool);
    ensures member.serial == old(member.serial);
    ensures count(ticket(pool + 1)) >= 0;
} by { execute(); simp(); }
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
fail: count(...) requires owning authority for that population
```
