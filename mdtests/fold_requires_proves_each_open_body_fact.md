# a fold's `requires` entries prove each body fact its fast path leaves open

Neither body fact of `digit` is stated, though both follow from the
requirements, so the fold leaves both open. One `requires` entry per body fact
proves it; a plain `by` would name both and ask for entries.

```c filename=fold_requires_proves_each_open_body_fact.c
void make(int32 x) { }
```

```click
verifying "fold_requires_proves_each_open_body_fact.c";
resource digit(n: int32) { fact n >= 0; fact n < 10; }
void make(int32 x) {
    requires x >= 1;
    requires x <= 5;
    produces digit(x);
} by {
    fold(digit(x)) {
        requires x >= 0 by simp;
        requires x < 10 by simp;
    }
    execute();
    simp();
}
```

```expect
pass
```
