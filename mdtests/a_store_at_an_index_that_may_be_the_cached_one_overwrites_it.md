# A store at an index that may be the cached one overwrites it

`0 <= j` admits `j == 0`, where `q[j] = 1` overwrites `q[0]` and the read
returns `1`. The implicit tail's attempt to prove `j != 0` before the store
misses, so the cached `7` is dropped and the false claim is refused on that
path.

```c filename=a_store_at_an_index_that_may_be_the_cached_one_overwrites_it.c
int read_first(int m, int j) {
    int *q = malloc(m * sizeof(int));
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
verifying "a_store_at_an_index_that_may_be_the_cached_one_overwrites_it.c";

int32 read_first(int32 m, int32 j) {
    requires 2 <= m;
    requires m <= 1000;
    requires 0 <= j;
    requires j < m;
    ensures result == 7;
}
```

```expect
fail: `ensures result == 7` failed for `read_first.ensures_0`
```
