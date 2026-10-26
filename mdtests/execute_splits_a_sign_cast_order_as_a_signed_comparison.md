# `execute` splits on a sign-cast order as a signed comparison

`(int)u < 0` compares `u`'s 32-bit word as `int32`. Assigned to a `bool`,
the comparison's two values are cases `execute` splits on, spelling the
case condition from the kernel's order. That spelling is `(int32)u < 0`:
the bare `u < 0` would lower to the `uint32` order, which is false, and
`execute` could not advance. Each case verifies.

```c filename=sign_bit.c
#include <stdbool.h>

bool sign_bit_set(unsigned int u) {
    bool set = (int)u < 0;
    return set;
}
```

```click
verifying "sign_bit.c";

bool sign_bit_set(uint32 u) {
    ensures result implies u > 2147483647u32;
    ensures u > 2147483647u32 implies result;
} by { execute(); auto(); }
```

```expect
pass
```
