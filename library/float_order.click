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

axiom float32_scale_right_lower(factor: float, x: float, bound: float) {
    requires x >= bound;
    requires isfinite(factor);
    requires float32_from_bits(0) < factor;
    ensures x * factor >= bound * factor;
}

axiom float32_scale_right_upper(factor: float, x: float, bound: float) {
    requires x <= bound;
    requires isfinite(factor);
    requires float32_from_bits(0) < factor;
    ensures x * factor <= bound * factor;
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

// A divisor on one side of zero ranges from the cited endpoint to that
// side's infinity.
// A finite numerator then gives quotients between zero and the rounded
// endpoint quotient, regardless of which of the two is larger.
axiom float32_bounded_reciprocal_lower(n: float, y: float, b: float, bound: float) {
    requires isfinite(n);
    requires (float32_from_bits(0) < b and b <= y) or (b < float32_from_bits(0) and y <= b);
    requires bound <= float32_from_bits(0);
    requires bound <= n / b;
    ensures n / y >= bound;
}

axiom float32_bounded_reciprocal_upper(n: float, y: float, b: float, bound: float) {
    requires isfinite(n);
    requires (float32_from_bits(0) < b and b <= y) or (b < float32_from_bits(0) and y <= b);
    requires float32_from_bits(0) <= bound;
    requires n / b <= bound;
    ensures n / y <= bound;
}

// Signed zero has one numeric value. The smallest positive value has bits 1.
axiom float32_strictly_positive_minimum(z: float, y: float) {
    requires z == float32_from_bits(0);
    requires z < y;
    ensures float32_from_bits(1) <= y;
}

axiom float64_bounded_reciprocal_lower(n: double, y: double, b: double, bound: double) {
    requires isfinite(n);
    requires (float64_from_bits(0u64) < b and b <= y) or (b < float64_from_bits(0u64) and y <= b);
    requires bound <= float64_from_bits(0u64);
    requires bound <= n / b;
    ensures n / y >= bound;
}

axiom float64_bounded_reciprocal_upper(n: double, y: double, b: double, bound: double) {
    requires isfinite(n);
    requires (float64_from_bits(0u64) < b and b <= y) or (b < float64_from_bits(0u64) and y <= b);
    requires float64_from_bits(0u64) <= bound;
    requires n / b <= bound;
    ensures n / y <= bound;
}

// Signed zero has one numeric value. The smallest positive value has bits 1.
axiom float64_strictly_positive_minimum(z: double, y: double) {
    requires z == float64_from_bits(0u64);
    requires z < y;
    ensures float64_from_bits(1u64) <= y;
}

// Finite ordered endpoints exclude infinities and NaNs. A square attains
// its maximum at an endpoint, and rounding preserves these orders.

axiom float32_finite_between(x: float, lo: float, hi: float) {
    requires x >= lo;
    requires x <= hi;
    requires isfinite(lo);
    requires isfinite(hi);
    ensures isfinite(x);
}

axiom float32_square_interval(x: float, lo: float, hi: float, upper: float) {
    requires x >= lo;
    requires x <= hi;
    requires isfinite(lo);
    requires isfinite(hi);
    requires lo * lo <= upper;
    requires hi * hi <= upper;
    ensures x * x >= float32_from_bits(0);
    ensures x * x <= upper;
}

axiom float64_finite_between(x: double, lo: double, hi: double) {
    requires x >= lo;
    requires x <= hi;
    requires isfinite(lo);
    requires isfinite(hi);
    ensures isfinite(x);
}

axiom float64_square_interval(x: double, lo: double, hi: double, upper: double) {
    requires x >= lo;
    requires x <= hi;
    requires isfinite(lo);
    requires isfinite(hi);
    requires lo * lo <= upper;
    requires hi * hi <= upper;
    ensures x * x >= float64_from_bits(0u64);
    ensures x * x <= upper;
}

// Integer conversion rounds monotonically, but may round adjacent inputs
// to the same value.
axiom int32_to_float32_le(a: int32, b: int32) {
    requires to_integer(a) <= to_integer(b);
    ensures (a as float) <= (b as float);
}
