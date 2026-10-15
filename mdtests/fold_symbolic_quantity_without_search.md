# Folding a symbolic quantity decides zero or positive without search

`fold(k of ok(x))` needs its quantity proved zero or positive. The check is an
exact lookup or the kernel's condition decision: `mint_positive` and
`mint_zero` state it in a `requires`; in `mint_have` it is hidden in a
predicate, and a `have` states it first.

```c filename=fold_symbolic_quantity.c
int32 mint_positive(int32 x, int32 k) { return x; }
int32 mint_zero(int32 x, int32 k) { return x; }
int32 mint_have(int32 x, int32 k) { return x; }
```

```click
predicate positive(k: int32) { 0 < k }

resource ok(x: int32) {
    fact x >= 0;
}

verifying "fold_symbolic_quantity.c";

int32 mint_positive(int32 x, int32 k) {
    requires x >= 0;
    requires 0 < k;
    produces k of ok(x);
} by {
    execute();
    fold(k of ok(x));
    simp();
}

int32 mint_zero(int32 x, int32 k) {
    requires x >= 0;
    requires k == 0;
    produces k of ok(x);
} by {
    execute();
    fold(k of ok(x));
    simp();
}

int32 mint_have(int32 x, int32 k) {
    requires x >= 0;
    requires positive(k);
    produces k of ok(x);
} by {
    execute();
    have 0 < k by { unfold(positive); simp(); }
    fold(k of ok(x));
    simp();
}
```

```expect
pass
```
