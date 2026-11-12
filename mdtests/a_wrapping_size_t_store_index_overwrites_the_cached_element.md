# A wrapping `size_t` store index overwrites the cached element

The Integer fact `k + 1 != 0` holds for every `size_t k`, but the `uint64`
word `k + 1u64` the store `q[k + 1] = 1` writes at wraps to `0` when `k` is
`SIZE_MAX`, where it overwrites `q[0]`. The disequality bridge carries an
Integer fact to the word fact only where the facts keep the word from
wrapping, so the store drops the cached `7`, and the case where the word is
`0` refuses the false claim.

```c filename=a_wrapping_size_t_store_index_overwrites_the_cached_element.c
#include <stddef.h>
#include <stdlib.h>

int read_first(size_t n, size_t k) {
    int *q = malloc(n * sizeof(int));
    if (q == 0) {
        return 7;
    }
    q[0] = 7;
    q[k + 1] = 1;
    int r = q[0];
    free(q);
    return r;
}
```

```click
verifying "a_wrapping_size_t_store_index_overwrites_the_cached_element.c";

int32 read_first(size_t n, size_t k) {
    requires 2u64 <= n and n <= 1000u64;
    requires to_integer(k + 1u64) < to_integer(n);
    requires k + 1 != 0;
    ensures result == 7;
}
```

```expect
fail: `ensures result == 7` failed for `read_first.ensures_0`
```
