# an index disequality does not separate an eight-byte store

The guard `k != j` excludes the element the store starts at, but the
eight-byte store at `&a[j]` also writes `a[j + 1]`, which the guard admits.
The quantified fact is refused.

```c filename=quantified_frame_rejects_a_wide_store_beside_the_excluded_cell.c
#include <stdint.h>

void clear_pair(int32_t *a, int32_t n, int32_t j) {
    int64_t *w;
    w = (int64_t *)(void *)&a[j];
    *w = 0;
}
```

```click
verifying "quantified_frame_rejects_a_wide_store_beside_the_excluded_cell.c";

void clear_pair(int32 *a, int32 n, int32 j) {
    requires 0 <= j;
    requires j + 1 < n;
    requires n <= 1000;
    owns a[0..n];
    ensures forall (k: int32) { 0 <= k and k < n and k != j implies a[k] == old(a[k]) };
} by {
    step();
    step();
    step();
    transport(
        forall (k: int32) { 0 <= k and k < n and k != j implies old(a[k]) == old(a[k]) },
        forall (k: int32) { 0 <= k and k < n and k != j implies a[k] == old(a[k]) }
    ) using {
        forall (k: int32) { 0 <= k and k < n and k != j implies old(a[k]) == old(a[k]) };
    }
    execute();
    simp();
}
```

```expect
fail: quantified frame: a leaf was not carried
```
