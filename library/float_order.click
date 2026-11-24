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
