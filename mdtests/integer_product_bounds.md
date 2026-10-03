# Exact product bounds from four explicit premises

The `integer_product_bounds` node checks a non-strict bound on a mathematical
`Integer` product from the constant endpoints of both operand intervals. The
four named premises give the left lower/upper and right lower/upper bounds.

The first lemma proves that a signed 64-by-32-bit mathematical product fits
signed 128 bits, a prerequisite for Bitcoin fee arithmetic. It does not prove
native `__int128` execution. The second multiplies separate machine observers:
`to_integer(a) * to_integer(b)` retains exact multiplication, and differs from
observing an already evaluated machine product. Explicit observer bounds are
requirements here; the certificate does not infer them from machine widths.
The last lemma exercises intervals crossing zero and both result directions.

A synthetic C identity wrapper retains that mathematical observer bound through
execution. Its source performs no wide multiplication; the contract is checked
without changing the program or treating a mathematical bound as machine
operation definedness.

```c filename=integer_product_bounds.c
long bounded_identity(long a, int b) {
    return a;
}
```

```click
verifying "integer_product_bounds.c";

theorem signed64_by_signed32_product(a: Integer, b: Integer) {
    requires -9223372036854775808 <= a;
    requires a <= 9223372036854775807;
    requires -2147483648 <= b;
    requires b <= 2147483647;
    ensures -170141183460469231731687303715884105728 <= a * b by {
        arithmetic_certificate special {
            premise 0: -9223372036854775808 <= a => -9223372036854775808 <= a;
            premise 1: a <= 9223372036854775807 => a <= 9223372036854775807;
            premise 2: -2147483648 <= b => -2147483648 <= b;
            premise 3: b <= 2147483647 => b <= 2147483647;
            integer_product_bounds bounds [0, 1, 2, 3] => -170141183460469231731687303715884105728 <= a * b;
            conclusion 0;
        }
    }
    ensures a * b <= 170141183460469231731687303715884105727 by {
        arithmetic_certificate special {
            premise 0: -9223372036854775808 <= a => -9223372036854775808 <= a;
            premise 1: a <= 9223372036854775807 => a <= 9223372036854775807;
            premise 2: -2147483648 <= b => -2147483648 <= b;
            premise 3: b <= 2147483647 => b <= 2147483647;
            integer_product_bounds bounds [0, 1, 2, 3] => a * b <= 170141183460469231731687303715884105727;
            conclusion 0;
        }
    }
}

theorem observed_machine_product(a: int64, b: int32) {
    requires -9223372036854775808 <= to_integer(a);
    requires to_integer(a) <= 9223372036854775807;
    requires -2147483648 <= to_integer(b);
    requires to_integer(b) <= 2147483647;
    ensures to_integer(a) * to_integer(b) <= 170141183460469231731687303715884105727 by {
        arithmetic_certificate special {
            premise 0: -9223372036854775808 <= to_integer(a) => -9223372036854775808 <= to_integer(a);
            premise 1: to_integer(a) <= 9223372036854775807 => to_integer(a) <= 9223372036854775807;
            premise 2: -2147483648 <= to_integer(b) => -2147483648 <= to_integer(b);
            premise 3: to_integer(b) <= 2147483647 => to_integer(b) <= 2147483647;
            integer_product_bounds bounds [0, 1, 2, 3] => to_integer(a) * to_integer(b) <= 170141183460469231731687303715884105727;
            conclusion 0;
        }
    }
}

theorem crossing_product(x: Integer, y: Integer) {
    requires -2 <= x;
    requires x <= 3;
    requires -4 <= y;
    requires y <= 5;
    ensures -12 <= x * y by {
        arithmetic_certificate special {
            premise 0: -2 <= x => -2 <= x;
            premise 1: x <= 3 => x <= 3;
            premise 2: -4 <= y => -4 <= y;
            premise 3: y <= 5 => y <= 5;
            integer_product_bounds bounds [0, 1, 2, 3] => -12 <= x * y;
            conclusion 0;
        }
    }
    ensures x * y <= 15 by {
        arithmetic_certificate special {
            premise 0: -2 <= x => -2 <= x;
            premise 1: x <= 3 => x <= 3;
            premise 2: -4 <= y => -4 <= y;
            premise 3: y <= 5 => y <= 5;
            integer_product_bounds bounds [0, 1, 2, 3] => x * y <= 15;
            conclusion 0;
        }
    }
}

int64 bounded_identity(int64 a, int32 b) {
    requires -9223372036854775808 <= to_integer(a);
    requires to_integer(a) <= 9223372036854775807;
    requires -2147483648 <= to_integer(b);
    requires to_integer(b) <= 2147483647;
    ensures to_integer(result) * to_integer(b) <= 170141183460469231731687303715884105727;
} by {
    execute();
    arithmetic_certificate special {
        premise 0: -9223372036854775808 <= to_integer(a) => -9223372036854775808 <= to_integer(a);
        premise 1: to_integer(a) <= 9223372036854775807 => to_integer(a) <= 9223372036854775807;
        premise 2: -2147483648 <= to_integer(b) => -2147483648 <= to_integer(b);
        premise 3: to_integer(b) <= 2147483647 => to_integer(b) <= 2147483647;
        integer_product_bounds bounds [0, 1, 2, 3] => to_integer(result) * to_integer(b) <= 170141183460469231731687303715884105727;
        conclusion 0;
    }
}
```

```expect
pass
```
