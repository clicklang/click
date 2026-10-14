# a fold's plain `by` proves the one body fact its fast path leaves open

`fold` checks each body fact exactly and never searches the proof context.
`x > 0` follows from the requirement `x >= 1`, but no fact states it, so the
fold leaves that body fact open. A plain `by` proves it, written over the
resource's arguments as the fold names them.

```c filename=fold_by_proves_its_one_open_body_fact.c
void make(int32 x) { }
```

```click
verifying "fold_by_proves_its_one_open_body_fact.c";
resource positive(n: int32) { fact n > 0; }
void make(int32 x) {
    requires x >= 1;
    produces positive(x);
} by {
    fold(positive(x)) by { simp(); }
    execute();
    simp();
}
```

```expect
pass
```
