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
