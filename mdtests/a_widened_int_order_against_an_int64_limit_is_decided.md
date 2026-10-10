# A widened `int` compared with an out-of-range `int64` constant is decided

An `int` widened to `int64` lies in the `int32` range, so comparing it with
`LONG_MAX`, or with any constant outside that range, has one answer. The
infeasible branch is not split, and `t > LONG_MAX` is false for any `int64`
`t`. A comparison the operand ranges do not decide still splits.

```c filename=widened_order.c
#include <limits.h>

int f(int x, long y) {
    if (x > LONG_MAX) {
        return 2;
    }
    if (x < -4294967296L) {
        return 3;
    }
    if (y > LONG_MAX) {
        return 4;
    }
    if (x > 2147483646L) {
        return 1;
    }
    return 0;
}
```

```click
verifying "widened_order.c";

int32 f(int32 x, int64 y) {
    ensures result == 0 or result == 1;
} by {
    execute();
    simp();
}
```

```expect
pass
```
