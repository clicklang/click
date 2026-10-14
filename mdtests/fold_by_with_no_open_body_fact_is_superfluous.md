# a fold's `by` is refused when its fast path leaves nothing open

The requirement states the body fact exactly, so the fold closes it without
help and the `by` proves nothing.

```c filename=fold_by_with_no_open_body_fact_is_superfluous.c
void make(int32 x) { }
```

```click
verifying "fold_by_with_no_open_body_fact_is_superfluous.c";
resource positive(n: int32) { fact n > 0; }
void make(int32 x) {
    requires x > 0;
    produces positive(x);
} by {
    fold(positive(x)) by { simp(); }
    execute();
    simp();
}
```

```expect
fail: this `fold`'s `by` is superfluous
```
