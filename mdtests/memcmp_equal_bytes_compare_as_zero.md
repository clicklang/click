# Equal byte ranges compare as zero

```c filename=compare.c
#include <string.h>
int ordered(void) {
    unsigned char left[1] = { 7 };
    unsigned char right[1] = { 7 };
    return memcmp(left, right, 1) == 0;
}
```

```click
import click::bytes;
verifying "compare.c";
int32 ordered() { ensures result == 1; } by {
    step_until(statement(2).call(memcmp, 0));
    let { result: cmp } = step(memcmp);
    have bytes::equal(left, 0u64, right, 0u64, 1u64) by {
        unfold(bytes::equal(left, 0u64, right, 0u64, 1u64));
        intro();
        intro();
        have k == 0u64 by { solve(); }
        rewrite(k, 0u64);
        solve();
    }
    apply(bytes::comparison_zero_when_equal(left, right, 1u64, cmp));
}
```

```expect
pass
```
