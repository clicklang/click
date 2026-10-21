# arithmetic rejects unbounded nonlinear expressions

A product neither factor of which the premises bound has no interval to
prove it defined. (`x == 0` and `y == 0` would bound both, and prove
`x * y == 0`.)

```click
theorem nonlinear_product_is_outside_arithmetic(x: int32, y: int32) {
    requires x == y;

    ensures to_integer(x * y) == to_integer(y * y) by {
        arithmetic() using {
            x == y;
        };
    }
}
```

```expect
fail: `x * y` must not overflow
```
