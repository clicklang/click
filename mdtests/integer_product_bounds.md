# Exact product bounds from four explicit premises

Arithmetic search expands to ordinary proof steps, with the selected premises
stated explicitly in `solve() using { ... }`.

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
        solve() using { -9223372036854775808 <= a; a <= 9223372036854775807; -2147483648 <= b; b <= 2147483647; };
    }
    ensures a * b <= 170141183460469231731687303715884105727 by {
        solve() using { -9223372036854775808 <= a; a <= 9223372036854775807; -2147483648 <= b; b <= 2147483647; };
    }
}

theorem observed_machine_product(a: int64, b: int32) {
    requires -9223372036854775808 <= to_integer(a);
    requires to_integer(a) <= 9223372036854775807;
    requires -2147483648 <= to_integer(b);
    requires to_integer(b) <= 2147483647;
    ensures to_integer(a) * to_integer(b) <= 170141183460469231731687303715884105727 by {
        solve() using { -9223372036854775808 <= to_integer(a); to_integer(a) <= 9223372036854775807; -2147483648 <= to_integer(b); to_integer(b) <= 2147483647; };
    }
}

theorem crossing_product(x: Integer, y: Integer) {
    requires -2 <= x;
    requires x <= 3;
    requires -4 <= y;
    requires y <= 5;
    ensures -12 <= x * y by {
        solve() using { -2 <= x; x <= 3; -4 <= y; y <= 5; };
    }
    ensures x * y <= 15 by {
        solve() using { -2 <= x; x <= 3; -4 <= y; y <= 5; };
    }
}

int64 bounded_identity(int64 a, int32 b) {
    requires -9223372036854775808 <= to_integer(a);
    requires to_integer(a) <= 9223372036854775807;
    requires -2147483648 <= to_integer(b);
    requires to_integer(b) <= 2147483647;
    ensures to_integer(result) * to_integer(b) <= 170141183460469231731687303715884105727;
} by {
    step_until(function.exit);
    solve() using { -9223372036854775808 <= to_integer(a); to_integer(a) <= 9223372036854775807; -2147483648 <= to_integer(b); to_integer(b) <= 2147483647; };
}
```

```expect
pass
```
