# Count identified members with equal exact arguments under wildcard authority

```c filename=field_family.c
int32 run() { int32 pool = 0; return 0; }
```

```click resource_semantics=authority
authorized resource ticket(pool: int32*, tag: int32) { field serial: int32; }
resource control(pool: int32*) { owns authority(ticket(pool, _)); }
verifying "field_family.c";
int32 run() { ensures result == 0; } by {
    step(); step();
    fold(authority(ticket(&pool, _)));
    have count(ticket(&pool, _)) == 0 by simp;
    let first = fold(ticket(&pool, 7), { serial: 1 });
    let second = fold(ticket(&pool, 7), { serial: 2 });
    have count(ticket(&pool, _)) == 2 by simp;
    have count(ticket(&pool, 7)) == 2 by simp;
    have count(ticket(&pool, 8)) == 0 by simp;
    have first.serial == 1 by simp;
    have second.serial == 2 by simp;
    fold(control(&pool));
    unfold(control(&pool));
    have count(ticket(&pool, _)) == 2 by simp;
    unfold(first);
    have count(ticket(&pool, _)) == 1 by simp;
    have count(ticket(&pool, 7)) == 1 by simp;
    have second.serial == 2 by simp;
    unfold(second);
    have count(ticket(&pool, _)) == 0 by simp;
    unfold(authority(ticket(&pool, _)));
    execute(); simp();
}
```

```expect
pass
```
