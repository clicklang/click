# A 128-bit order does not give a strict order

`a <= b` and `b <= c` give `a <= c` at 128 bits
(`a_128_bit_order_closes_through_its_integer_reading.md`), and not
`a < c`: all three may be equal.

```click
theorem not_strict(a: uint128, b: uint128, c: uint128) {
    requires a <= b;
    requires b <= c;
    ensures a < c;
}
```

```expect
fail: could not establish `a < c`
```
