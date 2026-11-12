# A stated `size_t` store search fact keeps the heap cell

The program of
`mdtests/a_size_t_store_search_miss_names_the_word_fact.md`, with the fact
its refusal names stated before `statement(3)`. `solve` proves
`((n - 1u64) as uint64) != 0u64` by cases on `n == 4u64 or n == 8u64`, and
the store keeps `q[0]`.

```c filename=a_stated_size_t_store_search_fact_keeps_the_heap_cell.c
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
verifying "a_stated_size_t_store_search_fact_keeps_the_heap_cell.c";

int32 read_first(size_t n) {
    requires 1u64 <= n and n <= 1000u64;
    requires n == 4u64 or n == 8u64;
    ensures result == 0 or result == 7 by {
        step(); step();
        if q == 0 {
            step_until(function.exit);
        } else {
            step_until(statement(3));
            have ((n - 1u64) as uint64) != 0u64 by solve();
            step_until(function.exit);
        }
    }
}
```

```expect
pass
```
