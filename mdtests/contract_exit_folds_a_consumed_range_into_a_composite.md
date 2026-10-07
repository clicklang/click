# A contract exit returns a composite folded from a consumed range

Control for the duplicate-return refusals: the range is consumed and the
composite is produced, so each cell is returned once, inside `wrap(p)`.

```c filename=fold_consumed.c
int32 f(int32* p) {
    return 0;
}
```

```click
resource wrap(p: int32*) {
    owns p[0..1];
}
verifying "fold_consumed.c";
int32 f(int32* p) {
    consumes p[0..1];
    produces wrap(p);
} by {
    execute();
    fold(wrap(p));
    simp();
}
```

```expect
pass
```
