# A contract-less helper with a concrete loop still executes

Concrete arguments and guards decided by the caller's facts still execute
without a helper contract. The loop body remains the same countdown.
These callers declare partial correctness with `diverges`: this fixture
checks execution and return values, and supplies no helper termination proof.

```c filename=include/drain.h
#ifndef DRAIN_H
#define DRAIN_H
static inline int32 drain_to_zero(int32 value) {
    while (value > 0) {
        value = value - 1;
    }
    return value;
}
#endif
```

```c filename=inline_helper_concrete_loop_without_contract.c
#include "include/drain.h"

int32 run(int32 n) {
    return drain_to_zero(3);
}

int32 run_zero(int32 n) {
    return drain_to_zero(n);
}
```

```click
verifying "inline_helper_concrete_loop_without_contract.c";

int32 run(int32 n) diverges {
    requires n >= 0;
    ensures result == 0;
} by {
    execute();
    simp();
}

int32 run_zero(int32 n) diverges {
    requires n == 0;
    ensures result == 0;
} by {
    execute();
    simp();
}
```

```expect
pass
```
