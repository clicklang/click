# a bare fold proves an unstated body fact by the implicit `auto`

The fold's fast path leaves `x > 0 or y > 0` open: no fact states it and it is
no condition the kernel decides. The implicit `auto` proves it at the fold, and
expansion prints that proof as the fold's `by`.

```c filename=fold_proves_an_unstated_body_fact_by_implicit_auto.c
void make(int32 x, int32 y) { }
```

```click
verifying "fold_proves_an_unstated_body_fact_by_implicit_auto.c";
resource either(n: int32, m: int32) { fact n > 0 or m > 0; }
void make(int32 x, int32 y) {
    requires x > 0;
    produces either(x, y);
} by {
    fold(either(x, y));
    execute();
    simp();
}
```

```expect
pass
```
