# a recursive inline helper with a contract is ranked by its measure

`drain` is a header `static inline` helper that calls itself. With a Click
contract, every call to it, its own recursive call included, applies that
contract, so the self-call owes the descent of its expression measure
`decreases level(n);` exactly as an ordinary recursive function's does
([`c_decreases_integer_measure_recursion.md`](c_decreases_integer_measure_recursion.md)).
Before inline helpers applied their contracts, such a measure was refused,
because the body ran at each call site and no call read the measure.
`run` calls the helper with a symbolic argument and applies its contract.

```c filename=include/drain.h
#ifndef DRAIN_H
#define DRAIN_H
static inline int32 drain(int32 n) {
    int32 result;
    if (n > 0) {
        result = drain(n - 1);
        return result;
    }
    return 0;
}
#endif
```

```c filename=inline_helper_expression_measure_recursion.c
#include "include/drain.h"

int32 run(int32 n) {
    return drain(n);
}
```

```click
verifying "inline_helper_expression_measure_recursion.c";

function level(n: int32) -> Integer {
    to_integer(n)
}

int32 drain(int32 n) {
    decreases level(n);
    requires n >= 0;
    ensures result == 0;
} by {
    step();
    branch then {
        have 0 <= n - 1 by {
            apply(int32_positive_predecessor_is_nonnegative(n)) using {
                n > 0;
            }
        }
        have 1 <= n by {
            arithmetic() using {
                n > 0;
            }
        }
        have defined(n - 1) by {
            apply(int32_nonnegative_subtract_within_value_is_defined(n, 1)) using {
                1 <= n;
            }
            simp();
        }
        have 0 <= level(n - 1) by {
            unfold(level(n - 1));
            apply(int32_less_equal_to_integer(0, n - 1)) using {
                0 <= n - 1;
            }
            simp();
        }
        have level(n - 1) < level(n) by {
            unfold(level(n - 1));
            unfold(level(n));
            apply(int32_subtract_to_integer(n, 1)) using {
                defined(n - 1);
            }
            simp() using {
                to_integer(n - 1) == to_integer(n) - to_integer(1);
            }
        }
        step();
        step();
        simp();
    } else {}
    step();
    simp();
}

int32 run(int32 n) {
    requires n >= 0;
    ensures result == 0;
} by {
    execute();
    simp();
}
```

```expect
pass
```
