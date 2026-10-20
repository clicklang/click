# normalize compares Integer sums exactly

`normalize` compares sums, differences, and negations of exact `Integer`
terms by their affine forms over the integers: terms reorder, regroup, and
cancel, and constants combine, with no modulus. A nonzero constant
difference makes the two sides unequal.

```c filename=normalize_compares_integer_sums_exactly.c
void unused(void) {}
```

```click
verifying "normalize_compares_integer_sums_exactly.c";

theorem observations(x: int32, y: uint64) {
    ensures 1 + to_integer(x) == to_integer(x) + 1 by { normalize(); }
    ensures to_integer(x) + (to_integer(y) + 3) == (to_integer(x) + to_integer(y)) + 3 by { normalize(); }
    ensures to_integer(x) - (to_integer(y) - 4) == to_integer(x) - to_integer(y) + 4 by { normalize(); }
    ensures -to_integer(x) + to_integer(x) == 0 by { normalize(); }
    ensures to_integer(x) + 1 != to_integer(x) by { normalize(); }
}

theorem integers(a: Integer, b: Integer) {
    ensures a + b == b + a by { normalize(); }
}
```

```expect
pass
```
