# operand bounds define a bounded difference and product

The positive next door to
`mdtests/a_bounded_wrapped_difference_does_not_define_the_signed_one.md` and
`mdtests/a_bounded_wrapped_product_does_not_define_the_signed_one.md`. With
both operands bounded, the integer difference and product stay inside
`int32`, so the signed operations are defined, and the wrapped value tested
first is the signed one: the bounds recorded on it carry to the result.

```c filename=operand_bounds_define_a_bounded_difference_and_product.c
int32 difference(int32 a, int32 b) {
    int32 d;
    d = (int32)((uint32)a - (uint32)b);
    if (d >= 0) {
        if (d <= 10) {
            return a - b;
        }
    }
    return 0;
}

int32 product(int32 a, int32 b) {
    int32 p;
    p = (int32)((uint32)a * (uint32)b);
    if (p >= 0) {
        if (p <= 10) {
            return a * b;
        }
    }
    return 0;
}
```

```click
verifying "operand_bounds_define_a_bounded_difference_and_product.c";

int32 difference(int32 a, int32 b) {
    requires 0 <= a;
    requires a <= 100;
    requires 0 <= b;
    requires b <= 100;
    ensures result >= 0;
    ensures result <= 10;
} by {
    execute();
    simp();
}

int32 product(int32 a, int32 b) {
    requires 0 <= a;
    requires a <= 100;
    requires 0 <= b;
    requires b <= 100;
    ensures result >= 0;
    ensures result <= 10;
} by {
    execute();
    simp();
}
```

```expect
pass
```
