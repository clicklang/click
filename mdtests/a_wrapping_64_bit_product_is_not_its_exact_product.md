# A wrapping 64-bit product is not its exact product

Without a bound on the exact product, a `uint64` product wraps, and its
observation need not be `to_integer(w) * to_integer(h)`: `w = h = 2^32`
gives zero. `solve` derives only the lower bound `0 <= to_integer(w) *
to_integer(h)` from the operands' type ranges
(`a_product_of_64_bit_values_is_its_exact_product.md`); the upper bound has
no source, so the identity is not planned and the postcondition is refused.

```c filename=product.c
uint64_t area(uint64_t w, uint64_t h) {
    return w * h;
}
```

```click
verifying "product.c";

uint64 area(uint64 w, uint64 h) {
    ensures to_integer(result) == to_integer(w) * to_integer(h);
}
```

```expect
fail: unclosed goal: to_integer(result) == (to_integer(w) * to_integer(h))
```
