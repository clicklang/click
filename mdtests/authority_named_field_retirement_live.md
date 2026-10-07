# Named members block authority retirement

```c filename=field_family.c
int32 run() { int32 pool = 0; return 0; }
```

```click resource_semantics=authority
authorized resource ticket(pool: int32*) { field serial: int32; }
verifying "field_family.c";
int32 run() { ensures result == 0; } by {
    step(); step();
    fold(authority(ticket(&pool)));
    let first = fold(ticket(&pool), { serial: 1 });
    unfold(authority(ticket(&pool)));
    execute(); simp();
}
```

```expect
fail: OutstandingMembers
```
