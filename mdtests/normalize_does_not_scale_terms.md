# normalize does not scale terms

`normalize` compares sums and differences after reordering and cancelling
them, for C machine values and for exact `Integer` terms, but a product is
one opaque operand. Proving `2 * to_integer(x) == to_integer(x) +
to_integer(x)` needs distributivity, so `normalize` refuses it within its
documented behavior; `arithmetic()` proves it.

```c filename=normalize_does_not_scale_terms.c
void unused(void) {}
```

```click
verifying "normalize_does_not_scale_terms.c";

theorem by_arithmetic(x: int32) {
    ensures 2 * to_integer(x) == to_integer(x) + to_integer(x) by { arithmetic(); }
}

theorem by_normalize(x: int32) {
    ensures 2 * to_integer(x) == to_integer(x) + to_integer(x) by { normalize(); }
}
```

```expect
fail: `normalize` goal did not normalize to true
```
