# A contract exit returns the range unfolded from a consumed composite

Control for the duplicate-return refusals: the composite is consumed and
its body range is produced, so the cell is returned once.

```c filename=unfold_consumed.c
int32 f(int32* p) {
    return 0;
}
```

```click
resource wrap(p: int32*) {
    owns p[0..1];
}
verifying "unfold_consumed.c";
int32 f(int32* p) {
    consumes wrap(p);
    produces p[0..1];
} by {
    unfold(wrap(p));
    execute();
    simp();
}
```

```expect
pass
```
