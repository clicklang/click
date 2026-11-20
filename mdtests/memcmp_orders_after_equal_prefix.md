# The first difference wins over a contrary later byte

```c filename=compare.c
#include <string.h>
int ordered(void) {
    unsigned char left[3] = { 9, 1, 255 };
    unsigned char right[3] = { 9, 2, 0 };
    return memcmp(left, right, 3) < 0;
}
```

```click
import click::bytes;
verifying "compare.c";
int32 ordered() { ensures result == 1; } by {
    step_until(statement(2).call(memcmp, 0).entry);
    let { result: cmp } = step(memcmp);
    have bytes::equal_range(left, right, 0u64, 1u64) by {
        unfold(bytes::equal_range(left, right, 0u64, 1u64));
        intro();
        intro();
        have k == 0u64 by { solve(); }
        rewrite(k, 0u64);
        solve();
    }
    apply(bytes::comparison_negative_after_prefix(left, right, 3u64, 1u64, cmp));
}
```

```expect
pass
```
