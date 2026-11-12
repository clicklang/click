# A product of 64-bit values is its exact product

A C function returns the product of two 64-bit values under a range
requirement on the exact product. The omitted proof plans the product's
in-range identity `to_integer(w * h) == to_integer(w) * to_integer(h)` at
`uint64` and `int64`, as it does for `+` and `-`. At `uint64` the lower bound
`0 <= to_integer(w) * to_integer(h)` is no requirement: `solve` derives it
from the operands' type ranges by `integer_product_bounds`, and `click
expand` writes those four range bounds, that certificate and the
`integer_operation_identity` step (`width_uniformity.rs`, the
`multiply_to_integer` family). The `int64` product's definedness and both
bounds come from the requirements.

```c filename=product.c
uint64_t area(uint64_t w, uint64_t h) {
    return w * h;
}

int64_t scaled(int64_t value, int64_t factor) {
    return value * factor;
}
```

```click
verifying "product.c";

uint64 area(uint64 w, uint64 h) {
    requires to_integer(w) * to_integer(h) <= 18446744073709551615;
    ensures to_integer(result) == to_integer(w) * to_integer(h);
}

int64 scaled(int64 value, int64 factor) {
    requires -9223372036854775808 <= to_integer(value) * to_integer(factor);
    requires to_integer(value) * to_integer(factor) <= 9223372036854775807;
    ensures to_integer(result) == to_integer(value) * to_integer(factor);
}
```

```expect
pass
```
