# The Linux kernel's `inline` attributes on a `static inline` helper

The Linux kernel defines `inline` as `inline` plus `gnu_inline`, `unused`,
and `no_instrument_function`. On a `static inline` function none of them
changes what the function computes: `gnu_inline` only selects when a
non-static inline definition is emitted, `unused` silences a warning, and
`no_instrument_function` omits profiling hooks. The helper bodies are still
checked at their call sites.

```c filename=include/helpers.h
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((no_instrument_function)) int add_one(int value) {
    return value + 1;
}
static inline __attribute__((__gnu_inline__)) __attribute__((__unused__)) __attribute__((__no_instrument_function__)) __attribute__((__always_inline__)) int add_two(int value) {
    return add_one(add_one(value));
}
```

```c filename=c_kernel_inline_attributes.c
#include "include/helpers.h"

int32 run(int32 value) {
    return add_two(value);
}
```

```click
verifying "c_kernel_inline_attributes.c";

int32 run(int32 value) {
    requires value < 100;
    ensures result == value + 2 by auto;
}
```

```expect
pass
```
