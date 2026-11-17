# A wide call result equality raises without a cast

A 64-bit equality reads both words at its own format, so the fact a call's
contract adds, `statement(0).call(add, 0).result ==
integer::uint64_wrapping_add(a, b)`, raises as written. The pure call on its
right is a `uint64` call read in that equality; raising it with an `int64` cast
would lower to a different term.

```c filename=a_wide_call_result_equality_raises_without_a_cast.c
#include <stdint.h>

uint64_t add(uint64_t a, uint64_t b) {
    return a + b;
}

uint64_t forward(uint64_t a, uint64_t b) {
    return add(a, b);
}
```

```click
import click::integer;

verifying "a_wide_call_result_equality_raises_without_a_cast.c";

uint64_t add(uint64_t a, uint64_t b) {
    ensures result == integer::uint64_wrapping_add(a, b);
}

uint64_t forward(uint64_t a, uint64_t b) {
    ensures result == integer::uint64_wrapping_add(a, b);
} by {
    step();
    step();
}
```

```expect
pass
```
