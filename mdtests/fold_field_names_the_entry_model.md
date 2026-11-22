# a fold field names the entry model of the instance it refolds

This fold selects the rank at function entry explicitly. A proof can also
[read the rank captured at the opening](fold_field_names_the_opened_model.md).

```c filename=fold_field_names_the_entry_model.c
void touch(int32* p) {
    p[0] = 1;
}
```

```click
verifying "fold_field_names_the_entry_model.c";

resource cell(p: int32*) {
    field rank: int32;
    owns p[0..1];
}

void touch(int32* p) {
    owns c: cell(p);
    ensures c.rank == old(c.rank);
} by {
    unfold(c);
    step_until(function.exit);
    let c = fold(cell(p), { rank: old(c.rank) });
    solve();
}
```

```expect
pass
```
