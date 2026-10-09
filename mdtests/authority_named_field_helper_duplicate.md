# A helper preserves an identified member and its proof fields

```c filename=helper.c
void preserve(int32* pool) {}
int32 run() { int32 pool = 0; preserve(&pool); return 0; }
```

```click
authorized resource ticket(pool: int32*) { field serial: int32; }
verifying "helper.c";
void preserve(int32* pool) {
    owns left: ticket(pool);
    owns right: ticket(pool);
    ensures left.serial == old(left.serial);
    ensures right.serial == old(right.serial);
} by { execute(); simp(); }
int32 run() { ensures result == 0; } by {
    step(); step();
    fold(authority(ticket(&pool)));
    let first = fold(ticket(&pool), { serial: 1 });
    step(preserve(&pool), { left: first, right: first });
    have first.serial == 1 by simp;
    have count(ticket(&pool)) == 1 by simp;
    unfold(first);
    unfold(authority(ticket(&pool)));
    execute(); simp();
}
```

```expect
fail: cannot supply two binders
```
