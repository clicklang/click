# Proof fields do not hide members from authority freshness

```c filename=field_family.c
int32 run() { int32 pool = 0; return 0; }
```

```click resource_semantics=authority
resource ticket(pool: int32*) { field serial: int32; }
verifying "field_family.c";
int32 run() { ensures result == 0; } by {
    step(); step();
    let first = fold(ticket(&pool), { serial: 1 });
    fold(authority(ticket(&pool)));
    execute(); simp();
}
```

```expect
fail: MembersAlreadyExisted
```
