# Rounding intervals from a quotient and remainder

```click

theorem derived_floor_from_remainder(n: Integer, d: Integer, q: Integer, r: Integer, value: Integer) {
    requires 0 < d;
    requires n == q * d + r;
    requires 1 - d <= r;
    requires r <= d - 1;
    requires r < 0 implies value == q + -1;
    requires 0 <= r implies value == q;
    ensures value * d <= n by {
        if r < 0 {
            have value == q + -1;
            apply(integer_multiply_add(q, -1, d));
            rewrite(value == q + -1);
            rewrite((q + -1) * d == q * d + -1 * d);
            arithmetic() using { n == q * d + r; 1 - d <= r; }
        } else {
            have 0 <= r by { arithmetic() using { not (r < 0); } }
            have value == q;
            rewrite(value == q);
            arithmetic() using { n == q * d + r; 0 <= r; }
        }
    }
    ensures n < (value + 1) * d by {
        if r < 0 {
            have value == q + -1;
            have value + 1 == q by { arithmetic() using { value == q + -1; } }
            rewrite(value + 1 == q);
            arithmetic() using { n == q * d + r; r < 0; }
        } else {
            have 0 <= r by { arithmetic() using { not (r < 0); } }
            have value == q;
            apply(integer_multiply_add(q, 1, d));
            rewrite(value == q);
            rewrite((q + 1) * d == q * d + 1 * d);
            arithmetic() using { n == q * d + r; r <= d - 1; }
        }
    }
}

theorem derived_ceiling_from_remainder(n: Integer, d: Integer, q: Integer, r: Integer, value: Integer) {
    requires 0 < d;
    requires n == q * d + r;
    requires 1 - d <= r;
    requires r <= d - 1;
    requires 0 < r implies value == q + 1;
    requires r <= 0 implies value == q;
    ensures n <= value * d by {
        if 0 < r {
            have value == q + 1;
            apply(integer_multiply_add(q, 1, d));
            rewrite(value == q + 1);
            rewrite((q + 1) * d == q * d + 1 * d);
            arithmetic() using { n == q * d + r; r <= d - 1; }
        } else {
            have r <= 0 by { arithmetic() using { not (0 < r); } }
            have value == q;
            rewrite(value == q);
            arithmetic() using { n == q * d + r; r <= 0; }
        }
    }
    ensures (value + -1) * d < n by {
        if 0 < r {
            have value == q + 1;
            have value + -1 == q by { arithmetic() using { value == q + 1; } }
            rewrite(value + -1 == q);
            arithmetic() using { n == q * d + r; 0 < r; }
        } else {
            have r <= 0 by { arithmetic() using { not (0 < r); } }
            have value == q;
            apply(integer_multiply_add(q, -1, d));
            rewrite(value == q);
            rewrite((q + -1) * d == q * d + -1 * d);
            arithmetic() using { n == q * d + r; 1 - d <= r; }
        }
    }
}
theorem use_floor_from_remainder(n: Integer, d: Integer, q: Integer, r: Integer, value: Integer) {
    requires 0 < d;
    requires n == q * d + r;
    requires 1 - d <= r;
    requires r <= d - 1;
    requires r < 0 implies value == q + -1;
    requires 0 <= r implies value == q;
    ensures value * d <= n by apply(integer_floor_from_remainder(n, d, q, r, value));
    ensures n < (value + 1) * d by apply(integer_floor_from_remainder(n, d, q, r, value));
}
theorem use_ceiling_from_remainder(n: Integer, d: Integer, q: Integer, r: Integer, value: Integer) {
    requires 0 < d;
    requires n == q * d + r;
    requires 1 - d <= r;
    requires r <= d - 1;
    requires 0 < r implies value == q + 1;
    requires r <= 0 implies value == q;
    ensures n <= value * d by apply(integer_ceiling_from_remainder(n, d, q, r, value));
    ensures (value + -1) * d < n by apply(integer_ceiling_from_remainder(n, d, q, r, value));
}
```

```expect
pass
```
