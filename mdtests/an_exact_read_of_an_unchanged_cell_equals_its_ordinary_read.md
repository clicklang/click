# An exact read of an unchanged cell equals its ordinary read

`p[0]` lowers to the read of the cell at its version point: the store to
`*q`, a separately owned object, leaves the cell unchanged, so after it the
ordinary read is still named by the entry state. `exact(p[0])` is the read of
the same cell named by the exit state itself, with no version walk
(`design/exact-reads.md`). They are different terms for the same value, and
the assumption-free load equality relates them, so the `have` holds.
`exact` composes with `old` and `at`: `old(exact(p[0]))` is the read named
by the entry state itself.

```c filename=an_exact_read_of_an_unchanged_cell_equals_its_ordinary_read.c
void touch(int *p, int *q) { *q = 1; }
```

```click
verifying "an_exact_read_of_an_unchanged_cell_equals_its_ordinary_read.c";
void touch(int32* p, int32* q) {
    owns p[0..1];
    owns q[0..1];
    ensures q[0] == 1;
    ensures p[0] == old(p[0]);
} by {
    step_until(function.exit);
    have exact(p[0]) == p[0] by close();
    have exact(p[0]) == old(p[0]) by close();
    have exact(q[0]) == 1 by close();
    have old(exact(p[0])) == old(p[0]) by close();
    have at(function.entry, exact(p[0])) == exact(p[0]) by close();
}
```

```expect
pass
```
