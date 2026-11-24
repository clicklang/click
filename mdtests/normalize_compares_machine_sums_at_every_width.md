# Comparing machine sums at every width

Machine comparison handles sums and differences of C machine values by their
affine forms modulo 2^width, at 32 and at 64 bits alike: terms reorder,
regroup, and cancel, and constants combine. A nonzero constant difference
makes the two sides unequal.

```c filename=normalize_compares_machine_sums_at_every_width.c
void unused(void) {}
```

```click
verifying "normalize_compares_machine_sums_at_every_width.c";

theorem words(x: int32, y: int32, z: uint32) {
    ensures 1 + x == x + 1 by { close(); }
    ensures x + (y + 1) == (y + x) + 1 by { close(); }
    ensures z - z == 0 by { close(); }
}

theorem wide(x: int64, y: int64, u: uint64, v: uint64) {
    ensures x + y == y + x by { close(); }
    ensures x + y - y == x by { close(); }
    ensures u + (v + 2) == (u + v) + 1 + 1 by { close(); }
    ensures u + 1 != u by { close(); }
}
```

```expect
pass
```
