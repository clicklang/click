# Integer bounds exclude constants

A named non-strict bound excludes constants strictly outside that bound. The
rule uses shared Integer operands, including nonlinear expressions, and does
not infer ambient machine ranges.

```click
import click::integer;

theorem positive_divisor_guards(d: int32) {
    requires d > 0;
    ensures to_integer(d) != 0 by {
        have 1 <= d by { solve() using { d > 0; }; }
        solve() using { 1 <= to_integer(d); };
    }
    ensures to_integer(d) != -1 by {
        have 1 <= d by { solve() using { d > 0; }; }
        solve() using { 1 <= to_integer(d); };
    }
}

theorem negative_bound_excludes_zero(x: Integer) {
    requires x <= -1;
    ensures x != 0 by {
        solve() using { x <= -1; };
    }
}
```

```expect
pass
```
