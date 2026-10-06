# Mathematical algebra does not distribute a wrapping machine product

The observations differ when x*y overflows u32. Each machine observation is
an opaque Integer atom, even though multiplication of separate observations
is a mathematical product.

```click
theorem false_machine_product(x: uint32, y: uint32) {
    ensures to_integer(x * y) == to_integer(x) * to_integer(y) by {
        arithmetic_certificate special {
            integer_polynomial_identity bounds [] => to_integer(x * y) == to_integer(x) * to_integer(y);
            conclusion 0;
        }
    }
}
```

```expect
fail: node 0 requires a true Integer polynomial identity
```
