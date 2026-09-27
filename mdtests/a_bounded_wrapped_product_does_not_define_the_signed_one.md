# a bounded wrapped product does not define the signed product

The multiplication twin of
`mdtests/a_bounded_wrapped_difference_does_not_define_the_signed_one.md`.
The unsigned product of two words wraps, so bounds on it converted to
`int32` bound a wrapped value: with `a == b == 65536` the wrapped product is
`0`, inside the tested window, while the signed `a * b` is `2^32`, which
overflows.

The overflow decision for a multiplication asked for the interval of the
product term, which read the bounds `0 <= p <= 10` recorded on that very
term, so the signed product below verified. The decision now multiplies the
operands' intervals over the integers.

```c filename=a_bounded_wrapped_product_does_not_define_the_signed_one.c
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
verifying "a_bounded_wrapped_product_does_not_define_the_signed_one.c";

int32 product(int32 a, int32 b) {
    ensures result >= 0;
} by {
    execute();
    simp();
}
```

```expect
fail: undefined behavior: signed overflow
```
