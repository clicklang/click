# A `size_t` store search miss names the `uint64` word fact

`q[0] = 7; q[n - 1] = 1;` with `n == 4u64 or n == 8u64` writes two different
elements, but the implicit tail's narrow closure (interval certificate,
order refutation, disequality bridge) does not split the disjunction, so the
store drops `q[0]` and the read is unknown. The refusal names the statement
and the `uint64` index-word fact the store reads, spelled from the two index
words; `mdtests/a_stated_size_t_store_search_fact_keeps_the_heap_cell.md`
states it.

```c filename=a_size_t_store_search_miss_names_the_word_fact.c
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
verifying "a_size_t_store_search_miss_names_the_word_fact.c";

int32 read_first(size_t n) {
    requires 1u64 <= n and n <= 1000u64;
    requires n == 4u64 or n == 8u64;
    ensures result == 0 or result == 7;
}
```

```expect
fail: statement(3) may have overwritten `q[0]`; it is kept if you state `have ((n - 1u64) as uint64) != 0u64 by { ... };` before statement(3)
```
