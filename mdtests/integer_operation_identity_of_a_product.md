# `integer_operation_identity` observes a product inside its type

A machine `*` is its exact product reduced modulo `2^32`, so when the
exact product lies in `uint32` the two are equal. The certificate names
the two bounds of `to_integer(x) * 2` inside `uint32`, as it does for a sum.

```click
theorem bounded(x: uint32) {
    requires x <= 1000u32;
    ensures to_integer(x * 2u32) == to_integer(x) * 2 by {
        have 0 <= to_integer(x) * 2;
        have to_integer(x) * 2 <= 4294967295;
        arithmetic_certificate rules {
            premise 0: 0 <= to_integer(x) * 2 => 0 <= to_integer(x) * 2;
            premise 1: to_integer(x) * 2 <= 4294967295 => to_integer(x) * 2 <= 4294967295;
            integer_operation_identity bounds [0, 1] => to_integer(x * 2u32) == to_integer(x) * 2;
            conclusion 0;
        }
    };
}
```

```expect
pass
```
