# A parenthesized comparison is a `bool` value only in a Rust sidecar

Rust reads `(x > 3)` as a `bool`. A C or C++ sidecar keeps a comparison a
proposition outside a `-> bool` body, so it is refused as an operand.

```c filename=positive.c
#include <stdbool.h>

bool positive(int x) { return x > 0; }
```

```click
verifying "positive.c";

bool positive(int32 x) {
    ensures result == (x > 0);
} by {
    execute();
    simp();
}
```

```expect
fail: expected `)`
```
