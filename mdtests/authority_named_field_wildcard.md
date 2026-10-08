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
    have count(ticket(&pool, _)) == 0;
    let first = fold(ticket(&pool, 7), { serial: 1 });
    let second = fold(ticket(&pool, 7), { serial: 2 });
    have count(ticket(&pool, _)) == 2;
    have count(ticket(&pool, 7)) == 2;
    have count(ticket(&pool, 8)) == 0;
    have first.serial == 1;
    have second.serial == 2;
    fold(control(&pool));
    unfold(control(&pool));
    have count(ticket(&pool, _)) == 2;
    unfold(first);
    have count(ticket(&pool, _)) == 1;
    have count(ticket(&pool, 7)) == 1;
    have second.serial == 2;
    unfold(second);
    have count(ticket(&pool, _)) == 0;
    unfold(authority(ticket(&pool, _)));
    execute(); simp();
}
```

```expect
pass
```
