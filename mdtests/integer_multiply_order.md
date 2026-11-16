# Multiplication order and fee caller bounds

The checked rule reads an ordered pair and the multiplier sign. Products may
place the factor on either side; constant folding is matched at the root.
This proves the wide-path input envelope for any bounded fee when
`0 <= at_size <= size`. It does not yet verify the upstream caller's fast path.

```click
import click::integer;

theorem checked_integer_multiply_order_nonnegative(a: Integer, b: Integer, factor: Integer) {
    requires a <= b;
    requires 0 <= factor;
    ensures a * factor <= b * factor by {
        solve() using { a <= b; 0 <= factor; };
    }
}

theorem checked_integer_multiply_order_nonpositive(a: Integer, b: Integer, factor: Integer) {
    requires a <= b;
    requires factor <= 0;
    ensures b * factor <= a * factor by {
        solve() using { a <= b; factor <= 0; };
    }
}

theorem checked_integer_scaled_product_bounds(value: Integer, amount: Integer, size: Integer, lower: Integer, upper: Integer) {
    requires lower <= value;
    requires value <= upper;
    requires lower <= 0;
    requires 0 <= upper;
    requires 0 <= amount;
    requires amount <= size;
    ensures lower * size <= value * amount by {
        apply(integer::multiply_order_nonnegative(lower, value, amount));
        have lower * size <= lower * amount by {
            solve() using { amount <= size; lower <= 0; };
        }
        solve() using { lower * size <= lower * amount; lower * amount <= value * amount; };
    }
    ensures value * amount <= upper * size by {
        apply(integer::multiply_order_nonnegative(value, upper, amount));
        have upper * amount <= upper * size by {
            solve() using { amount <= size; 0 <= upper; };
        }
        solve() using { value * amount <= upper * amount; upper * amount <= upper * size; };
    }
}

theorem fee_caller_division_bounds(fee: Integer, at_size: Integer, size: Integer) {
    requires -9223372036854775808 <= fee;
    requires fee <= 9223372036854775807;
    requires 0 <= at_size;
    requires at_size <= size;
    requires 1 <= size;
    requires size != 0;
    ensures -9223372036854775808 * size <= fee * at_size by {
        apply(integer::scaled_product_bounds(fee, at_size, size, -9223372036854775808, 9223372036854775807));
    }
    ensures fee * at_size <= 9223372036854775807 * size by {
        apply(integer::scaled_product_bounds(fee, at_size, size, -9223372036854775808, 9223372036854775807));
    }
    ensures -9223372036854775808 <= truncating_quotient(fee * at_size, size) by {
        apply(integer::scaled_product_bounds(fee, at_size, size, -9223372036854775808, 9223372036854775807));
        apply(integer::positive_divisor_quotient_lower(fee * at_size, size, -9223372036854775808));
    }
    ensures truncating_quotient(fee * at_size, size) <= 9223372036854775807 by {
        apply(integer::scaled_product_bounds(fee, at_size, size, -9223372036854775808, 9223372036854775807));
        apply(integer::positive_divisor_quotient_upper(fee * at_size, size, 9223372036854775807));
    }
}
```

```expect
pass
```
