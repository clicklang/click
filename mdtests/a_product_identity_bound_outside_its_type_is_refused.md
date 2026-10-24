# A product identity bound outside its type is refused

`integer_operation_identity` needs both named bounds of a product inside
the operation's type. An upper bound of `4294967296` is one past `uint32`,
so the certificate does not show that the product does not wrap.

```click
theorem past_the_type(x: uint32) {
    requires x <= 1000u32;
    ensures to_integer(x * 2u32) == to_integer(x) * 2 by {
        have 0 <= to_integer(x) * 2 by auto();
        have to_integer(x) * 2 <= 4294967296 by auto();
        arithmetic_certificate rules {
            premise 0: 0 <= to_integer(x) * 2 => 0 <= to_integer(x) * 2;
            premise 1: to_integer(x) * 2 <= 4294967296 => to_integer(x) * 2 <= 4294967296;
            integer_operation_identity bounds [0, 1] => to_integer(x * 2u32) == to_integer(x) * 2;
            conclusion 0;
        }
    };
}
```

```expect
fail: arithmetic certificate rejected: node 0 requires
```
