# Identified unary members have disjoint private memory

```c filename=private_members.c
int32 run() {
    int32 pool = 0;
    int32* p = malloc(8);
    if (p == 0) return 0;
    p[0] = 1;
    p[1] = 2;
    int32 result = p[0] + p[1];
    free(p);
    return result;
}
```

```click resource_semantics=authority
resource ticket(pool: int32*, tag: int32) {
    field cell: int32*;
    field serial: int32;
    owns cell[0..1];
}
verifying "private_members.c";
int32 run() { ensures result == 0 or result == 3; } by {
    step(); step(); step(); step();
    branch then { execute(); simp(); } else {}
    step(); step();
    fold(authority(ticket(&pool, _)));
    let first = fold(ticket(&pool, 7), { cell: p, serial: 1 });
    let second = fold(ticket(&pool, 7), { cell: p + 1, serial: 2 });
    have count(ticket(&pool, _)) == 2 by simp;
    have count(ticket(&pool, 7)) == 2 by simp;
    have first.serial == 1 by simp;
    have second.serial == 2 by simp;
    unfold(first);
    have count(ticket(&pool, _)) == 1 by simp;
    have second.serial == 2 by simp;
    unfold(second);
    unfold(authority(ticket(&pool, _)));
    execute(); simp();
}
```

```expect
pass
```
