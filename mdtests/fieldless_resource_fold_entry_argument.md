# An explicit entry argument survives current binding capture

```c filename=entry_scalar.c
void value(int32 x) { x = 8; }
```

```click
verifying "entry_scalar.c";
resource seven(n: int32) { fact n == 7; }
void value(int32 x) {
    consumes seven(x);
    ensures 1 == 1;
} by {
    unfold(seven(x));
    step();
    fold(seven(old(x)));
    execute(); simp();
}
```

```expect
pass
```
