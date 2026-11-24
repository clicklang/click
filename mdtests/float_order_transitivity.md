# Ordered float bounds are transitive

```click
import click::float_order;

theorem check_float32_le_le(a: float, b: float, c: float) {
    requires a <= b;
    requires b <= c;
    ensures a <= c by apply(float_order::float32_le_le(a, b, c));
}

theorem check_float32_le_lt(a: float, b: float, c: float) {
    requires a <= b;
    requires b < c;
    ensures a < c by apply(float_order::float32_le_lt(a, b, c));
}

theorem check_float32_lt_le(a: float, b: float, c: float) {
    requires a < b;
    requires b <= c;
    ensures a < c by apply(float_order::float32_lt_le(a, b, c));
}

theorem check_float64_le_le(a: double, b: double, c: double) {
    requires a <= b;
    requires b <= c;
    ensures a <= c by apply(float_order::float64_le_le(a, b, c));
}

theorem check_float64_le_lt(a: double, b: double, c: double) {
    requires a <= b;
    requires b < c;
    ensures a < c by apply(float_order::float64_le_lt(a, b, c));
}

theorem check_float64_lt_le(a: double, b: double, c: double) {
    requires a < b;
    requires b <= c;
    ensures a < c by apply(float_order::float64_lt_le(a, b, c));
}
```

```expect
pass
```
