# A store at the last `size_t` heap element keeps the first

The `size_t` counterpart of
`mdtests/a_store_at_the_last_heap_element_keeps_the_first.md`. `q[n - 1]`
addresses the array through a 64-bit scaled index and `q[0]` through a
constant offset of whole elements. The store keeps a cached element only on
a stated disequality of the two index words compared as `uint64` (or as
`int64` for a `long` index): it reads `((n - 1u64) as uint64) != 0u64`
exactly, in either orientation, or a strict order of the two words.

With no proof body, the implicit tail sees the store drop `q[0]`, proves the
`uint64` word fact by arithmetic before the store, and runs the store again.
`click expand` writes that `have` before the store's `step()`.
`mdtests/a_size_t_store_index_fact_variants_keep_the_first.md` covers a
`size_t` index variable, a `long` index, and stated word and Integer facts.

```c filename=a_store_at_the_last_size_t_heap_element_keeps_the_first.c
#include <stddef.h>
#include <stdlib.h>

int read_first(size_t n) {
    int *q = malloc(n * sizeof(int));
    if (q == 0) {
        return 0;
    }
    q[0] = 7;
    q[n - 1] = 1;
    int r = q[0];
    free(q);
    return r;
}
```

```click
verifying "a_store_at_the_last_size_t_heap_element_keeps_the_first.c";

int32 read_first(size_t n) {
    requires 2u64 <= n and n <= 1000u64;
    ensures result == 0 or result == 7;
}
```

```expect
pass
```
