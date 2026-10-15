# a fold's `requires` entries prove each body fact its fast path leaves open

Neither body fact of `pair` is stated, though both follow from the
requirement, and neither is a condition the kernel decides, so the fold leaves
both open. One `requires` entry per body fact
proves it; a plain `by` would name both and ask for entries.

```c filename=fold_requires_proves_each_open_body_fact.c
void make(int32 x, int32 y) { }
```

```click
verifying "fold_requires_proves_each_open_body_fact.c";
resource pair(n: int32, m: int32) { fact n > 0 or m > 0; fact m > 0 or n > 0; }
void make(int32 x, int32 y) {
    requires x > 0;
    produces pair(x, y);
} by {
    fold(pair(x, y)) {
        requires x > 0 or y > 0 by simp;
        requires y > 0 or x > 0 by simp;
    }
    execute();
    simp();
}
```

```expect
pass
```
