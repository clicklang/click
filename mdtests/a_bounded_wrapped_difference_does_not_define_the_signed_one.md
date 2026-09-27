# a bounded wrapped difference does not define the signed difference

A signed `a - b` is undefined when the integer difference leaves `int32`.
The unsigned difference of the same two words wraps instead, and converts
to `int32` without complaint, so bounds on that converted difference bound a
*wrapped* value:

    d = (int32)((uint32)a - (uint32)b);   // a - b modulo 2^32
    if (0 <= d <= 10) return a - b;       // defined?

With `a == INT_MIN` and `b == INT_MAX - 4` the wrapped difference is `5`,
inside the tested window, while `a - b` is `-2^32 + 5`, which overflows.

Both differences are the one kernel term `a - b`, and the overflow decision
for a subtraction asked for the interval of that term. The interval reads
the bounds recorded on the term itself first, and `0 <= d <= 10` had just
recorded them, so the decision answered "does not overflow" and the
subtraction below verified. The decision now ranges the operands and
subtracts over the integers, which is the question the definedness of the
subtraction asks; the bounds on the wrapped difference say nothing about it.

`mdtests/operand_bounds_define_a_bounded_difference_and_product.md` is the
positive next door: with the operands bounded, the same subtraction is
defined and returns the bounded value.

```c filename=a_bounded_wrapped_difference_does_not_define_the_signed_one.c
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
```

```click
verifying "a_bounded_wrapped_difference_does_not_define_the_signed_one.c";

int32 difference(int32 a, int32 b) {
    ensures result >= 0;
} by {
    execute();
    simp();
}
```

```expect
fail: undefined behavior: signed overflow
```
