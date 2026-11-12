# A `size_t` store at an index that may be the cached one overwrites it

`j < n` admits `j == 0`, where `q[j] = 1` overwrites `q[0]` and the read
returns `1`. The implicit tail's attempt to prove `j != 0u64` before the
store misses, so the cached `7` is dropped and the false claim is refused on
that path, as for an `int` index in
`mdtests/a_store_at_an_index_that_may_be_the_cached_one_overwrites_it.md`.

```c filename=a_size_t_store_at_an_index_that_may_be_the_cached_one_overwrites_it.c
#include <stddef.h>
#include <stdlib.h>

int read_first(size_t n, size_t j) {
    int *q = malloc(n * sizeof(int));
    if (q == 0) {
        return 7;
    }
    q[0] = 7;
    q[j] = 1;
    int r = q[0];
    free(q);
    return r;
}
```

```click
verifying "a_size_t_store_at_an_index_that_may_be_the_cached_one_overwrites_it.c";

int32 read_first(size_t n, size_t j) {
    requires 2u64 <= n and n <= 1000u64;
    requires j < n;
    ensures result == 7;
}
```

```expect
fail: `ensures result == 7` failed for `read_first.ensures_0`
```
