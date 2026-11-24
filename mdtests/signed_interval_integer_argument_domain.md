# Integer argument domains for observed signed operations

```click
import click::integer;
theorem step_link(x: int32, y: int32) {
    requires x < y;
    ensures to_integer(x + 1) <= to_integer(y) by {
        have to_integer(x) + 1 <= to_integer(y) by {
            apply(integer::lt_step_le(to_integer(x), to_integer(y)));
        }
        have -2147483648 <= to_integer(x) + 1 by {
            have -2147483648 <= to_integer(x) by close();
            close() using { -2147483648 <= to_integer(x); };
        }
        have to_integer(x) + 1 <= 2147483647 by {
            have to_integer(y) <= 2147483647 by close();
            close() using { to_integer(x) + 1 <= to_integer(y); to_integer(y) <= 2147483647; };
        }
        have to_integer((x + 1) as int32) == to_integer(x) + 1 by {
            close() using { -2147483648 <= to_integer(x) + 1; to_integer(x) + 1 <= 2147483647; };
        }
        have defined(x + 1) by close();
        apply(integer::le_substitute(to_integer(x) + 1, to_integer(y), to_integer((x + 1) as int32), to_integer(y)));
    }
}
```

```expect
pass
```
