# An external wildcard contract preserves distinct named identities and counts

```c filename=helper.c
extern void preserve(int32* pool);
int32 run() { int32 pool = 0; preserve(&pool); return 0; }
```

```click resource_semantics=authority
authorized resource ticket(pool: int32*, tag: int32) { field serial: int32; }
verifying "helper.c";
extern void preserve(int32* pool) {
    owns authority(ticket(pool, _));
    owns left: ticket(pool, 7);
    owns right: ticket(pool, 7);
    ensures left.serial == old(left.serial);
    ensures right.serial == old(right.serial);
    ensures count(ticket(pool, _)) == old(count(ticket(pool, _)));
    ensures count(ticket(pool, 7)) == old(count(ticket(pool, 7)));
}
int32 run() { ensures result == 0; } by {
    step(); step();
    fold(authority(ticket(&pool, _)));
    let first = fold(ticket(&pool, 7), { serial: 1 });
    let second = fold(ticket(&pool, 7), { serial: 2 });
    let framed = fold(ticket(&pool, 8), { serial: 3 });
    step(preserve(&pool), { left: first, right: second });
    have first.serial == 1;
    have second.serial == 2;
    have count(ticket(&pool, _)) == 3;
    have count(ticket(&pool, 7)) == 2;
    have count(ticket(&pool, 8)) == 1;
    have framed.serial == 3;
    unfold(first); unfold(second); unfold(framed);
    unfold(authority(ticket(&pool, _)));
    execute(); simp();
}
```

```expect
pass
```
