# Integer parameters, fields and results read machine arithmetic exactly

An argument for an `Integer` parameter of a pure function or theorem, an
`Integer` constructor field, and the body of a `-> Integer` function each
expect an Integer, so machine arithmetic there is exact: at `a ==
INT32_MAX`, `a + 1` is `2147483648`, not an overflow. This holds for a
library theorem's parameters and for the built-in `truncating_remainder`
as well.

```click
import click::integer;

function twice(x: Integer) -> Integer {
    x + x
}

function successor(x: int32) -> Integer {
    x + 1
}

spec enum Total {
    Sum(Integer),
}

function total_value(t: Total) -> Integer {
    match t {
        Total::Sum(n) => n,
    }
}

theorem an_integer_parameter_takes_the_exact_sum(a: int32) {
    requires a == 2147483647;
    ensures twice(a + 1) == 4294967296 by {
        unfold(twice(a + 1));
        solve();
    }
}

theorem an_integer_result_is_exact(a: int32) {
    requires a == 2147483647;
    ensures successor(a) == 2147483648 by {
        unfold(successor(a));
        solve();
    }
}

theorem an_integer_field_holds_the_exact_sum(a: int32) {
    requires a == 2147483647;
    ensures total_value(Total::Sum(a + 1)) == 2147483648 by {
        unfold(total_value(Total::Sum(a + 1)));
        solve();
    }
}

theorem a_library_theorem_takes_the_exact_sum(a: uint32, b: uint32) {
    ensures 0 <= truncating_remainder(a + b, 3) by {
        have 0 <= a + b by auto();
        apply(integer::nonnegative_dividend_remainder(a + b, 3));
    }
}
```

```expect
pass
```
