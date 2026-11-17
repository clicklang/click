# An explicitly reconstructed nonnegative remainder

The quotient needs no separate sign premise: the positive divisor, nonnegative
dividend and stated residue range establish the unique truncating remainder.

```click
import click::integer;
theorem reconstruct(n: Integer, d: Integer, q: Integer, r: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires 0 <= n;
    requires 0 <= r;
    requires r <= d - 1;
    requires n == q * d + r;
    ensures truncating_remainder(n, d) == r by {
        apply(integer::nonnegative_remainder_from_reconstruction(n, d, q, r)) using {
            d != 0; 1 <= d; 0 <= n; 0 <= r; r <= d - 1; n == q * d + r;
        };
    }
}
```

```expect
pass
```
