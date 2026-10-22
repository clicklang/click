# Checked named consumption reaches callers and nested helper boundaries

```c filename=helper.c
void retire(int32* pool) {}
void nested(int32* pool) { retire(pool); }
int32 run() { int32 pool = 0; nested(&pool); return 0; }
```

```click
authorized resource ticket(pool: int32*, tag: int32) { field serial: int32; }
verifying "helper.c";
void retire(int32* pool) {
    owns authority(ticket(pool, _));
    consumes member: ticket(pool, 7);
    ensures to_integer(count(ticket(pool, _))) == to_integer(old(count(ticket(pool, _))) - 1);
    ensures to_integer(count(ticket(pool, 7))) == to_integer(old(count(ticket(pool, 7))) - 1);
} by { unfold(member); execute(); simp(); }
void nested(int32* pool) {
    owns authority(ticket(pool, _));
    consumes member: ticket(pool, 7);
    ensures to_integer(count(ticket(pool, _))) == to_integer(old(count(ticket(pool, _))) - 1);
    ensures to_integer(count(ticket(pool, 7))) == to_integer(old(count(ticket(pool, 7))) - 1);
} by { step({ member: member }); execute(); simp(); }
int32 run() { ensures result == 0; } by {
    step(); step();
    fold(authority(ticket(&pool, _)));
    let first = fold(ticket(&pool, 7), { serial: 1 });
    let second = fold(ticket(&pool, 7), { serial: 2 });
    step({ member: first });
    have second.serial == 2;
    have to_integer(count(ticket(&pool, _))) == 1;
    have to_integer(count(ticket(&pool, 7))) == 1;
    unfold(second); unfold(authority(ticket(&pool, _)));
    execute(); simp();
}
```

```expect
pass
```
