# Creating a counted named member through a helper requires authority

```c filename=private_helper.c
void make(int32* pool, int32* p) {}
int32 run() {
    int32 pool = 0;
    int32* p = malloc(8);
    if (p == 0) return 0;
    p[0] = 1;
    p[1] = 2;
    make(&pool, p);
    int32 result = p[0] + p[1];
    free(p);
    return result;
}
```

```click resource_semantics=authority
resource ticket(pool: int32*, p: int32*) {
    field serial: int32;
    owns p[0..1];
}
resource control(pool: int32*) { owns authority(ticket(pool, _)); }
verifying "private_helper.c";
void make(int32* pool, int32* p) {
    consumes p[0..1];
    produces member: ticket(pool, p);
    ensures member.serial == 1;
} by { let member = fold(ticket(pool, p), { serial: 1 }); execute(); simp(); }
int32 run() { ensures result == 0 or result == 3; } by {
    step(); step(); step(); step();
    branch { then { execute(); simp(); } else {} }
    step(); step();
    fold(authority(ticket(&pool, _)));
    let second = fold(ticket(&pool, p + 1), { serial: 2 });
    fold(control(&pool));
    let { member: first } = step(make(&pool, p), {});

    have second.serial == 2 by simp;
    unfold(control(&pool));
    have count(ticket(&pool, _)) == 2 by simp;
    unfold(second);
    unfold(authority(ticket(&pool, _)));
    execute(); simp();
}
```

```expect
fail: missing resource fact `owns authority(ticket(&pool, _))`
```
