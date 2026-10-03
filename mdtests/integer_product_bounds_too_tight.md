# A false product range is refused

The endpoint product `3 * 5` exceeds the claimed upper bound. Listing all four
available premises does not make this certificate valid.

```click
theorem too_tight_product(x: Integer, y: Integer) {
    requires -2 <= x;
    requires x <= 3;
    requires -4 <= y;
    requires y <= 5;
    ensures x * y <= 14 by {
        arithmetic_certificate special {
            premise 0: -2 <= x => -2 <= x;
            premise 1: x <= 3 => x <= 3;
            premise 2: -4 <= y => -4 <= y;
            premise 3: y <= 5 => y <= 5;
            integer_product_bounds bounds [0, 1, 2, 3] => x * y <= 14;
            conclusion 0;
        }
    }
}
```

```expect
fail: does not state what its rule derives from its inputs
```
