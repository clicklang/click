# `size_t` store index fact variants keep the first element

Variants of `mdtests/a_store_at_the_last_size_t_heap_element_keeps_the_first.md`.
The implicit tail proves `j != 0u64` for a `size_t` index variable
(`read_j`) and the `int64` word fact for a `long` index (`signed_long`)
before the store. A stated word fact `((n - 1) as uint64) != 0` is read
directly by the store (`stated_word`); a stated Integer fact `n - 1 != 0`
reaches the word fact through the disequality bridge where the facts keep
`n - 1` from wrapping (`stated_integer`).

```c filename=a_size_t_store_index_fact_variants_keep_the_first.c
#include <stddef.h>
#include <stdlib.h>

int read_j(size_t n, size_t j) {
    int *q = malloc(n * sizeof(int));
    if (q == 0) {
        return 0;
    }
    q[0] = 7;
    q[j] = 1;
    int r = q[0];
    free(q);
    return r;
}

int signed_long(long n) {
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

int stated_word(size_t n) {
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

int stated_integer(size_t n) {
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
verifying "a_size_t_store_index_fact_variants_keep_the_first.c";

int32 read_j(size_t n, size_t j) {
    requires 2u64 <= n and n <= 1000u64;
    requires 1u64 <= j and j < n;
    ensures result == 0 or result == 7;
}

int32 signed_long(int64 n) {
    requires 2 <= n and n <= 1000;
    ensures result == 0 or result == 7;
}

int32 stated_word(size_t n) {
    requires 2u64 <= n and n <= 1000u64;
    ensures result == 0 or result == 7;
} by {
    have ((n - 1) as uint64) != 0 by solve();
}

int32 stated_integer(size_t n) {
    requires 2u64 <= n and n <= 1000u64;
    ensures result == 0 or result == 7;
} by {
    have n - 1 != 0 by solve();
}
```

```expect
pass
```
