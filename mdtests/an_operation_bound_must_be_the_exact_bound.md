# An operation bound must be the exact bound

`x <= 1000 * (x / 1000) + 999` is the upper bound a quotient by 1000 takes
from its operand. A certificate that states `+ 998` instead is refused: it is
not a bound any quotient, shift, or remainder in it gives.

```click
theorem tighter_than_the_floor(v: uint64) {
    requires 4294967296u64 <= v;
    ensures 4294967u64 <= v / 1000u64 by {
        arithmetic_certificate {
            negated_goal => to_integer((v / 1000u64)) < to_integer(4294967u64);
            scale 0 by 1000 => (1000 * (to_integer((v / 1000u64)) + 1)) <= (1000 * to_integer(4294967u64));
            premise 0: 4294967296 <= to_integer(v) => 4294967296 <= to_integer(v);
            operation_bound => to_integer(v) <= ((1000 * to_integer((v / 1000u64))) + 998);
            add 1, 2 => ((1000 * (to_integer((v / 1000u64)) + 1)) + 4294967296) <= ((1000 * to_integer(4294967u64)) + to_integer(v));
            add 4, 3 => ((1000 * (to_integer((v / 1000u64)) + 1)) + 4294967296 + to_integer(v)) <= ((1000 * to_integer(4294967u64)) + to_integer(v) + ((1000 * to_integer((v / 1000u64))) + 998));
            conclusion 5;
        }
    };
}
```

```expect
fail: integer certificate operation bound must be
```
