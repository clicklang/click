# Defined unsigned multiplication does not imply a non-wrapping observation

```click
import click::integer;

theorem invalid_unsigned_product(a: uint32, b: uint32) {
    requires defined(a * b);
    ensures to_integer(a * b) == to_integer(a) * to_integer(b) by {
        apply(uint32_multiply_to_integer(a, b));
    }
}
```

```expect
fail: proof step
```
