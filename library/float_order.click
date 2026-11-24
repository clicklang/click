// Each true ordered comparison excludes NaN from both operands.
// Infinities and signed zeros obey the same transitivity laws.
axiom float32_le_le(a: float, b: float, c: float) {
    requires a <= b;
    requires b <= c;
    ensures a <= c;
}

axiom float32_le_lt(a: float, b: float, c: float) {
    requires a <= b;
    requires b < c;
    ensures a < c;
}

axiom float32_lt_le(a: float, b: float, c: float) {
    requires a < b;
    requires b <= c;
    ensures a < c;
}

axiom float64_le_le(a: double, b: double, c: double) {
    requires a <= b;
    requires b <= c;
    ensures a <= c;
}

axiom float64_le_lt(a: double, b: double, c: double) {
    requires a <= b;
    requires b < c;
    ensures a < c;
}

axiom float64_lt_le(a: double, b: double, c: double) {
    requires a < b;
    requires b <= c;
    ensures a < c;
}

// Rounded addition is monotone in each operand on these ordered domains.
// Finite endpoints exclude the infinities that could form an indeterminate sum.
axiom float32_add_lower(x: float, y: float, a: float, b: float) {
    requires x >= a;
    requires y >= b;
    requires isfinite(a);
    requires isfinite(b);
    ensures x + y >= a + b;
}

axiom float32_add_upper(x: float, y: float, a: float, b: float) {
    requires x <= a;
    requires y <= b;
    requires isfinite(a);
    requires isfinite(b);
    ensures x + y <= a + b;
}

axiom float64_add_lower(x: double, y: double, a: double, b: double) {
    requires x >= a;
    requires y >= b;
    requires isfinite(a);
    requires isfinite(b);
    ensures x + y >= a + b;
}

axiom float64_add_upper(x: double, y: double, a: double, b: double) {
    requires x <= a;
    requires y <= b;
    requires isfinite(a);
    requires isfinite(b);
    ensures x + y <= a + b;
}

axiom float32_scale_lower(factor: float, x: float, bound: float) {
    requires x >= bound;
    requires isfinite(factor);
    requires float32_from_bits(0) < factor;
    ensures factor * x >= factor * bound;
}

axiom float32_scale_upper(factor: float, x: float, bound: float) {
    requires x <= bound;
    requires isfinite(factor);
    requires float32_from_bits(0) < factor;
    ensures factor * x <= factor * bound;
}

// Rounded subtraction is monotone in the left operand and reverses order
// in the right. Finite endpoints exclude same-sign infinity subtraction.
axiom float32_sub_lower(x: float, y: float, a: float, b: float) {
    requires x >= a;
    requires y <= b;
    requires isfinite(a);
    requires isfinite(b);
    ensures x - y >= a - b;
}

axiom float32_sub_upper(x: float, y: float, a: float, b: float) {
    requires x <= a;
    requires y >= b;
    requires isfinite(a);
    requires isfinite(b);
    ensures x - y <= a - b;
}

axiom float64_sub_lower(x: double, y: double, a: double, b: double) {
    requires x >= a;
    requires y <= b;
    requires isfinite(a);
    requires isfinite(b);
    ensures x - y >= a - b;
}

axiom float64_sub_upper(x: double, y: double, a: double, b: double) {
    requires x <= a;
    requires y >= b;
    requires isfinite(a);
    requires isfinite(b);
    ensures x - y <= a - b;
}

// A strict double bound may round to equality after narrowing.
axiom float64_narrow_le(a: double, b: double) {
    requires a <= b;
    ensures (a as float) <= (b as float);
}

axiom float64_narrow_lt(a: double, b: double) {
    requires a < b;
    ensures (a as float) <= (b as float);
}

axiom float32_lt_to_le(a: float, b: float) {
    requires a < b;
    ensures a <= b;
}

axiom float64_lt_to_le(a: double, b: double) {
    requires a < b;
    ensures a <= b;
}

// Positive products are monotone in both operands. Over finite ordered
// intervals the rounded product extrema come from their four corners.
axiom float32_positive_product_lower(x: float, y: float, a: float, b: float) {
    requires x >= a;
    requires y >= b;
    requires isfinite(a);
    requires isfinite(b);
    requires float32_from_bits(0) < a;
    requires float32_from_bits(0) < b;
    ensures x * y >= a * b;
}

axiom float32_product_lower(x: float, y: float, a: float, b: float, c: float, d: float, bound: float) {
    requires x >= a;
    requires y >= b;
    requires x <= c;
    requires y <= d;
    requires isfinite(a);
    requires isfinite(b);
    requires isfinite(c);
    requires isfinite(d);
    requires bound <= a * b;
    requires bound <= a * d;
    requires bound <= c * b;
    requires bound <= c * d;
    ensures x * y >= bound;
}

axiom float32_product_upper(x: float, y: float, a: float, b: float, c: float, d: float, bound: float) {
    requires x >= a;
    requires y >= b;
    requires x <= c;
    requires y <= d;
    requires isfinite(a);
    requires isfinite(b);
    requires isfinite(c);
    requires isfinite(d);
    requires a * b <= bound;
    requires a * d <= bound;
    requires c * b <= bound;
    requires c * d <= bound;
    ensures x * y <= bound;
}

axiom float64_positive_product_lower(x: double, y: double, a: double, b: double) {
    requires x >= a;
    requires y >= b;
    requires isfinite(a);
    requires isfinite(b);
    requires float64_from_bits(0u64) < a;
    requires float64_from_bits(0u64) < b;
    ensures x * y >= a * b;
}

axiom float64_product_lower(x: double, y: double, a: double, b: double, c: double, d: double, bound: double) {
    requires x >= a;
    requires y >= b;
    requires x <= c;
    requires y <= d;
    requires isfinite(a);
    requires isfinite(b);
    requires isfinite(c);
    requires isfinite(d);
    requires bound <= a * b;
    requires bound <= a * d;
    requires bound <= c * b;
    requires bound <= c * d;
    ensures x * y >= bound;
}

axiom float64_product_upper(x: double, y: double, a: double, b: double, c: double, d: double, bound: double) {
    requires x >= a;
    requires y >= b;
    requires x <= c;
    requires y <= d;
    requires isfinite(a);
    requires isfinite(b);
    requires isfinite(c);
    requires isfinite(d);
    requires a * b <= bound;
    requires a * d <= bound;
    requires c * b <= bound;
    requires c * d <= bound;
    ensures x * y <= bound;
}

// Dividing a positive finite numerator by a positive value decreases to
// positive zero as the divisor increases to positive infinity.
axiom float32_reciprocal_lower(n: float, y: float, b: float) {
    requires isfinite(n);
    requires float32_from_bits(0) < n;
    requires float32_from_bits(0) < b;
    requires b <= y;
    ensures n / y >= float32_from_bits(0);
}

axiom float32_reciprocal_upper(n: float, y: float, b: float) {
    requires isfinite(n);
    requires float32_from_bits(0) < n;
    requires float32_from_bits(0) < b;
    requires b <= y;
    ensures n / y <= n / b;
}

axiom float32_quotient_lower(x: float, y: float, a: float, b: float, c: float, d: float, bound: float) {
    requires x >= a;
    requires y >= b;
    requires x <= c;
    requires y <= d;
    requires isfinite(a);
    requires isfinite(b);
    requires isfinite(c);
    requires isfinite(d);
    requires float32_from_bits(0) < b or d < float32_from_bits(0);
    requires bound <= a / b;
    requires bound <= a / d;
    requires bound <= c / b;
    requires bound <= c / d;
    ensures x / y >= bound;
}

axiom float32_quotient_upper(x: float, y: float, a: float, b: float, c: float, d: float, bound: float) {
    requires x >= a;
    requires y >= b;
    requires x <= c;
    requires y <= d;
    requires isfinite(a);
    requires isfinite(b);
    requires isfinite(c);
    requires isfinite(d);
    requires float32_from_bits(0) < b or d < float32_from_bits(0);
    requires a / b <= bound;
    requires a / d <= bound;
    requires c / b <= bound;
    requires c / d <= bound;
    ensures x / y <= bound;
}

axiom float64_reciprocal_lower(n: double, y: double, b: double) {
    requires isfinite(n);
    requires float64_from_bits(0) < n;
    requires float64_from_bits(0) < b;
    requires b <= y;
    ensures n / y >= float64_from_bits(0);
}

axiom float64_reciprocal_upper(n: double, y: double, b: double) {
    requires isfinite(n);
    requires float64_from_bits(0) < n;
    requires float64_from_bits(0) < b;
    requires b <= y;
    ensures n / y <= n / b;
}

axiom float64_quotient_lower(x: double, y: double, a: double, b: double, c: double, d: double, bound: double) {
    requires x >= a;
    requires y >= b;
    requires x <= c;
    requires y <= d;
    requires isfinite(a);
    requires isfinite(b);
    requires isfinite(c);
    requires isfinite(d);
    requires float64_from_bits(0) < b or d < float64_from_bits(0);
    requires bound <= a / b;
    requires bound <= a / d;
    requires bound <= c / b;
    requires bound <= c / d;
    ensures x / y >= bound;
}

axiom float64_quotient_upper(x: double, y: double, a: double, b: double, c: double, d: double, bound: double) {
    requires x >= a;
    requires y >= b;
    requires x <= c;
    requires y <= d;
    requires isfinite(a);
    requires isfinite(b);
    requires isfinite(c);
    requires isfinite(d);
    requires float64_from_bits(0) < b or d < float64_from_bits(0);
    requires a / b <= bound;
    requires a / d <= bound;
    requires c / b <= bound;
    requires c / d <= bound;
    ensures x / y <= bound;
}
