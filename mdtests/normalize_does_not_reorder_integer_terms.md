# normalize does not reorder Integer terms

`normalize` evaluates constants and compares the two sides as terms. Proving
`1 + to_integer(x) == to_integer(x) + 1` needs commutativity, which is
arithmetic rather than evaluation, so `normalize` refuses it within its
documented behavior; `arithmetic()` proves it.

```c filename=normalize_does_not_reorder_integer_terms.c
void unused(void) {}
```

```click
verifying "normalize_does_not_reorder_integer_terms.c";

theorem by_arithmetic(x: int32) {
    ensures 1 + to_integer(x) == to_integer(x) + 1 by { arithmetic(); }
}

theorem by_normalize(x: int32) {
    ensures 1 + to_integer(x) == to_integer(x) + 1 by { normalize(); }
}
```

```expect
fail: `normalize` goal did not normalize to true
```
