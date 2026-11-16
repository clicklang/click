# Public signed-int32 certificate composition

Arithmetic search expands to ordinary proof steps, with the selected premises
stated explicitly in `solve() using { ... }`.

```click
import click::integer;

theorem signed_direct_compound(n: int32) {
    requires defined(n + 1);
    requires 0 <= to_integer(n + 1);
    ensures 0 <= to_integer(n + 1) by {
        solve() using { 0 <= to_integer(n + 1); };
    }
}

theorem signed_pair_compound(n: int32) {
    requires 0 <= n;
    requires n <= 100;
    ensures to_integer(n + 1) <= to_integer(n + 2) by {
        solve() using {
            0 <= n;
            n <= 100;
        };
    }
}

theorem machine_to_integer_then_integer_arithmetic(x: int32) {
    requires 0 <= x;
    ensures 0 <= to_integer(x) + 1 by {
        have to_integer(0) <= to_integer(x);
        solve() using { to_integer(0) <= to_integer(x); };
    }
}
```

```expect
pass
```
