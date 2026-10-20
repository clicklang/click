# Unsigned widening retains a certificate's exact conclusion

The bounded certificate comparison includes the unsigned zero extension.
A positive Integer observation excludes zero in either inequality spelling.

```click
import click::integer;
theorem positive_is_nonzero(x: int32) {
    requires 1 <= to_integer((uint64)(uint32)x);
    ensures not (to_integer((uint64)(uint32)x) == 0) by {
        arithmetic_certificate rules {
            premise 0: 1 <= to_integer((uint64)(uint32)x) => 1 <= to_integer((uint64)(uint32)x);
            integer_bound_exclusion bounds [0] => not (to_integer((uint64)(uint32)x) == 0);
            conclusion 0;
        }
    }
}
theorem widened_positive_is_unequal_to_zero(x: int32) {
    requires 1 <= to_integer((uint64)(uint32)x);
    ensures to_integer((uint64)(uint32)x) != 0 by {
        arithmetic_certificate rules {
            premise 0: 1 <= to_integer((uint64)(uint32)x) => 1 <= to_integer((uint64)(uint32)x);
            integer_bound_exclusion bounds [0] => to_integer((uint64)(uint32)x) != 0;
            conclusion 0;
        }
    }
}
```

```expect
pass
```
