# Count two separately identified members with equal family arguments

```c filename=field_family.c
int32 run() { int32 pool = 0; return 0; }
```

```click
authorized resource ticket(pool: int32*) { field serial: int32; }
resource control(pool: int32*) { owns authority(ticket(pool)); }
verifying "field_family.c";
int32 run() { ensures result == 0; } by {
    step(); step();
    fold(authority(ticket(&pool)));
    have count(ticket(&pool)) == 0;
    let first = fold(ticket(&pool), { serial: 1 });
    let second = fold(ticket(&pool), { serial: 2 });
    have count(ticket(&pool)) == 2;
    have first.serial == 1;
    have second.serial == 2;
    fold(control(&pool));
    unfold(control(&pool));
    have count(ticket(&pool)) == 2;
    unfold(first);
    have count(ticket(&pool)) == 1;
    have second.serial == 2;
    unfold(second);
    have count(ticket(&pool)) == 0;
    unfold(authority(ticket(&pool)));
    execute(); simp();
}
```

```expect
pass
```
