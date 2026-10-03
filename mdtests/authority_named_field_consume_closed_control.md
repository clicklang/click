# Named member ownership cannot consume a member under a closed control

```c filename=field_family.c
int32 run() { int32 pool = 0; return 0; }
```

```click resource_semantics=authority
resource ticket(pool: int32*) { field serial: int32; }
resource control(pool: int32*) { owns authority(ticket(pool)); }
verifying "field_family.c";
int32 run() { ensures result == 0; } by {
    step(); step();
    fold(authority(ticket(&pool)));
    let first = fold(ticket(&pool), { serial: 1 });
    fold(control(&pool));
    unfold(first);
    execute(); simp();
}
```

```expect
fail: Requires owns authority(ticket(...))
```
