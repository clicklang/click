# `simp` does not open a call guarantee off its path

The companion of `simp_opens_a_call_guarantee_under_its_path_condition.md`
asks for the guarantee's consequent on the branch where `r != 0`. There the
antecedent `r == 0` is not available, and the consequent is false: `probe`
returned 1 without writing `cell[1]`, which need not equal
`at(before_probe, cell[0])`. Modus ponens needs the antecedent exactly, so
`simp` refuses.

```c filename=probe.c
int32 probe(int32 *cell) {
    if (cell[0] == 0) return 1;
    cell[1] = cell[0];
    cell[0] = 0;
    return 0;
}
```

```c filename=use_probe.c
int32 use_probe(int32 *cell) {
    int32 r;
    r = probe(cell);
    if (r == 0) {
        return cell[1];
    }
    return 0;
}
```

```click
verifying "probe.c";
verifying "use_probe.c";

int32 probe(int32 *cell) {
    owns cell[0..2];
    ensures result == 0 or result == 1;
    ensures result == 0 implies cell[0] == 0 and cell[1] == old(cell[0]);
} by auto;

int32 use_probe(int32 *cell) {
    owns cell[0..2];
    ensures result == 0 or result == old(cell[0]);
} by {
    step();
    mark before_probe;
    step();
    if c(r) == 0 {
        have cell[0] == 0 and cell[1] == at(before_probe, cell[0]);
        execute();
        simp();
    } else {
        have cell[0] == 0 and cell[1] == at(before_probe, cell[0]);
        execute();
        simp();
    }
}
```

```expect
fail: could not establish `cell[0] == 0 and cell[1] == at(before_probe, cell[0])`
```
