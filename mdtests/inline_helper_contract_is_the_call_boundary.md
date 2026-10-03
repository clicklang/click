# an inline helper's contract is its call boundary

A `static inline` helper with a verified Click contract is called through that
contract, like any other function. `drain_to_zero` holds a loop with a symbolic
guard. Running its body at the call site with `n` unknown would unroll that
loop symbolically. Applying the contract instead costs one call step, however
long the loop runs: the caller meets `requires value >= 0` and receives
`result == 0`. The helper's loop is ranked and certified once, in its own
proof.

The caller is listed before the helper. The helper's contract is a callee
assumption for every selected caller, so whether a call applies the contract
does not depend on which function the sidecar verifies first.

A helper with no contract still runs its body at the call site
([`c_decreases_loop_inline_helper.md`](c_decreases_loop_inline_helper.md)).

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

int32 drain_to_zero(int32 value) {
    requires value >= 0;
    ensures result == 0;
} by {
    loop {
        decreases value;
        invariant value >= 0;
        initialize by simp;
        preserve by {
            have 0 <= value - 1 by {
                apply(int32_positive_predecessor_is_nonnegative(value)) using { value > 0; }
            }
            step();
            close_invariants by {
                both { arithmetic() using { 0 <= value; } }
                and {
                    both { arithmetic() using { 0 <= value; } }
                    and { arithmetic() using { 0 <= value; } }
                }
            }
        }
    }
    step();
    simp();
}
```

```expect
pass
```
