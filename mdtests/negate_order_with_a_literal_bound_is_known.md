# One selected order rule and its known result
```click
import click::integer;
theorem negate_constant_bound(n: Integer, d: Integer) {
    requires -d != 0;
    requires truncating_quotient(n, -d) <= 4;
    ensures -4 <= -truncating_quotient(n, -d) by {
        apply(integer::negate_order(truncating_quotient(n, -d), 4)) using {
            truncating_quotient(n, -d) <= 4; -d != 0;
        };
        known();
    }
}
```
```expect
pass
```
