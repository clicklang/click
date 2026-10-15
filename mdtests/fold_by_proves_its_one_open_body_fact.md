# a fold's plain `by` proves the one body fact its fast path leaves open

`fold` checks each body fact exactly, or by the kernel's condition decision,
and never searches the proof context. `x > 0 or y > 0` follows from the
requirement `x > 0`, but it is no condition and no fact states it, so the fold
leaves that body fact open. A plain `by` proves it, written over the
resource's arguments as the fold names them.

```c filename=fold_by_proves_its_one_open_body_fact.c
void make(int32 x, int32 y) { }
```

```click
verifying "fold_by_proves_its_one_open_body_fact.c";
resource either(n: int32, m: int32) { fact n > 0 or m > 0; }
void make(int32 x, int32 y) {
    requires x > 0;
    produces either(x, y);
} by {
    fold(either(x, y)) by { simp(); }
    execute();
    simp();
}
```

```expect
pass
```
