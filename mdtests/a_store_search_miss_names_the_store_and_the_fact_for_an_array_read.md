# A store search miss names the store and the fact for an array read

`a[0] = 7; a[j - 1] = 1;` with `1 <= j <= 4` and `j != 1` writes two
different elements of the automatic array, so `int r = a[0];` is the `7`.
The implicit tail spells `((j - 1) as int32) != 0` before the store and
misses it: its narrow closure does not use `j != 1`. The store drops the
cached `a[0]` and the claim is refused.

The refusal names the statement and the fact the search spelled. Stating it
there, `step_until(statement(2)); have ... by solve();`, keeps the cell.

```c filename=a_store_search_miss_names_the_store_and_the_fact_for_an_array_read.c
int read_first(int j) {
    int a[4];
    a[0] = 7;
    a[j - 1] = 1;
    int r = a[0];
    return r;
}
```

```click
verifying "a_store_search_miss_names_the_store_and_the_fact_for_an_array_read.c";

int32 read_first(int32 j) {
    requires 1 <= j;
    requires j <= 4;
    requires j != 1;
    ensures result == 7;
}
```

```expect
fail: statement(2) may have overwritten `a`; it is kept if you state `have not ((j - 1) as int32) == (0 as int32) by { ... };` before statement(2)
```
