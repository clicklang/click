# Integer bounds exclude constants

A named non-strict bound excludes constants strictly outside that bound. The
rule uses shared Integer operands, including nonlinear expressions, and does
not infer ambient machine ranges.

```click
theorem positive_divisor_guards(d: int32) {
    requires d > 0;
    ensures to_integer(d) != 0 by {
        have 1 <= d by { arithmetic() using { d > 0; } }
        apply(int32_less_equal_to_integer(1, d));
        arithmetic_certificate special {
            premise 0: 1 <= to_integer(d) => 1 <= to_integer(d);
            integer_bound_exclusion bounds [0] => to_integer(d) != 0;
            conclusion 0;
        }
    }
    ensures to_integer(d) != -1 by {
        have 1 <= d by { arithmetic() using { d > 0; } }
        apply(int32_less_equal_to_integer(1, d));
        arithmetic_certificate special {
            premise 0: 1 <= to_integer(d) => 1 <= to_integer(d);
            integer_bound_exclusion bounds [0] => to_integer(d) != -1;
            conclusion 0;
        }
    }
}

theorem negative_bound_excludes_zero(x: Integer) {
    requires x <= -1;
    ensures x != 0 by {
        arithmetic_certificate special {
            premise 0: x <= -1 => x <= -1;
            integer_bound_exclusion bounds [0] => x != 0;
            conclusion 0;
        }
    }
}
```

```expect
pass
```
