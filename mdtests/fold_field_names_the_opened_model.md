# A fold field can read the model captured by its opening

The write changes the cell while the open instance keeps its captured rank.
The fold supplies that rank to the restored instance.

```c filename=fold_field_names_the_opened_model.c
void touch(int32* p) {
    p[0] = 1;
}
```

```click
verifying "fold_field_names_the_opened_model.c";

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
    let c = fold(cell(p), { rank: c.rank });
    close();
}
```

```expect
pass
```
