# A member-only helper writes private memory under a closed population control

```c filename=private_helper.c
void bump(int32* pool, int32* p) { p[0] = 7; }
int32 run() {
    int32 pool = 0;
    int32* p = malloc(8);
    if (p == 0) return 0;
    p[0] = 1;
    p[1] = 2;
    bump(&pool, p);
    int32 result = p[0] + p[1];
    free(p);
    return result;
}
```

```click
authorized resource ticket(pool: int32*, p: int32*) {
    field serial: int32;
    owns p[0..1];
}
resource control(pool: int32*) { owns authority(ticket(pool, _)); }
verifying "private_helper.c";
void bump(int32* pool, int32* p) {
    owns member: ticket(pool, p);
    ensures member.serial == old(member.serial);
    ensures p[0] == 7;
} by { unfold(member); step(); fold(member); execute(); simp(); }
int32 run() { ensures result == 0 or result == 9; } by {
    step(); step(); step(); step();
    branch then { execute(); simp(); } else {}
    step(); step();
    fold(authority(ticket(&pool, _)));
    let first = fold(ticket(&pool, p), { serial: 1 });
    let second = fold(ticket(&pool, p + 1), { serial: 2 });
    fold(control(&pool));
    step(bump(&pool, p), { member: first });
    have first.serial == 1;
    have second.serial == 2;
    unfold(control(&pool));
    have count(ticket(&pool, _)) == 2;
    unfold(first); unfold(second);
    unfold(authority(ticket(&pool, _)));
    execute(); simp();
}
```

```expect
pass
```
