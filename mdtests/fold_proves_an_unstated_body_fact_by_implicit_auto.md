# a bare fold proves an unstated body fact by the implicit `auto`

The fold's fast path leaves `x > 0` open; the implicit `auto` proves it at the
fold, and expansion prints that proof as the fold's `by`.

```c filename=fold_proves_an_unstated_body_fact_by_implicit_auto.c
void make(int32 x) { }
```

```click
verifying "fold_proves_an_unstated_body_fact_by_implicit_auto.c";
resource positive(n: int32) { fact n > 0; }
void make(int32 x) {
    requires x >= 1;
    produces positive(x);
} by {
    fold(positive(x));
    execute();
    simp();
}
```

```expect
pass
```
