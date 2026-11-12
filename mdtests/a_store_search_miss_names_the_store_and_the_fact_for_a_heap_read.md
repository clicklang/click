# A store search miss names the store and the fact for a heap read

`q[0] = 7; q[m - 1] = 1;` with `1 <= m` and `m != 1` writes two different
elements, so the later read `int r = q[0];` is the `7`. The store keeps the
cached `q[0]` only on a stated disequality of the two `int32` index words.
The implicit tail spells `((m - 1) as int32) != 0` before the store and tries
to prove it by arithmetic, but its narrow closure does not use `m != 1`, so
the store drops `q[0]` and the read is unknown.

The refusal names the statement whose store dropped the cell and the exact
fact the search spelled, so a proof can state it before that statement with
`step_until(statement(3)); have ... by solve();`, which `solve` proves from
`m != 1`.

```c filename=a_store_search_miss_names_the_store_and_the_fact_for_a_heap_read.c
int read_first(int m) {
    int *q = malloc(m * sizeof(int));
    if (q == 0) {
        return 0;
    }
    q[0] = 7;
    q[m - 1] = 1;
    int r = q[0];
    free(q);
    return r;
}
```

```click
verifying "a_store_search_miss_names_the_store_and_the_fact_for_a_heap_read.c";

int32 read_first(int32 m) {
    requires 1 <= m;
    requires m <= 1000;
    requires m != 1;
    ensures result == 0 or result == 7;
}
```

```expect
fail: statement(3) may have overwritten `q[0]`; it is kept if you state `have not (let integer_value: Integer = to_integer(((m - 1) as int32)); integer_value) == 0 by { ... };` before statement(3)
```
