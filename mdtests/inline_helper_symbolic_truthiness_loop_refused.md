# A symbolic truthiness guard in an inline helper fails promptly

The unchanged helper body has a symbolic guard and no contract. Executing
its call must refuse that guard promptly rather than accumulate an unrolled
path. The diagnostic names the helper and explains the needed call boundary.

```c filename=include/drain.h
#ifndef DRAIN_H
#define DRAIN_H
static inline int32 drain_to_zero(int32 value) {
    while (value) {
        value = value - 1;
    }
    return value;
}
#endif
```

```c filename=inline_helper_contract_is_the_call_boundary.c
#include "include/drain.h"

int32 run(int32 n) {
    return drain_to_zero(n);
}
```

```click
verifying "inline_helper_contract_is_the_call_boundary.c";

int32 run(int32 n) {
    requires n >= 0;
    ensures result == 0;
} by {
    execute();
    simp();
}


```

```expect
fail: loop guard cannot be decided at the call site
```
