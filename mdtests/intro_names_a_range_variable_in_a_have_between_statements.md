# `intro()` names a range quantifier's variable in a `have` between statements

A `have` stated between C statements is lowered at the execution frontier,
which records no lowering provenance for its binders. `intro()` still names
a range quantifier's variable as written, so the body can cite it: here
`instantiate` specializes `memset`'s postcondition at `k` and the value
conjunct closes the goal.

```c filename=fill.c
#include <string.h>

void fill(unsigned char *dst) {
    memset(dst, 7, 4);
}
```

```click
import click::bytes;
verifying "fill.c";

void fill(uint8* dst) {
    owns dst[0..4];
    ensures bytes::all_equal(dst, 0u64, 4u64, 7u8);
} by {
    step();
    have (0u64..4u64).all(|k| { dst[k] == 7 }) by {
        intro();
        intro();
        instantiate((0u64..4u64).all(|k| { defined(dst[k]) and dst[k] == 7 }), k);
        assumption();
    }
    execute();
    simp();
}
```

```expect
pass
```
