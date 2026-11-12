# A store index bound and disequality keep a cached element

`a[0] = 7; a[j - 1] = 1;` with `1 <= j <= 4` and `j != 1` writes two
different elements of the automatic array, so `int r = a[0];` is the `7`.
The implicit tail spells `((j - 1) as int32) != 0` before the store, and its
narrow closure proves it: the Integer certificate's
`less_than_from_not_equal` makes `1 <= j` strict by `j != 1`, so `2 <= j`.
The store keeps `a[0]`. A disjunction in place of `j != 1` is still a miss,
and the refusal names it
(`a_store_search_miss_names_the_store_and_the_fact_for_an_array_read.md`).

```c filename=a_store_index_bound_and_disequality_keep_a_cached_element.c
int read_first(int j) {
    int a[4];
    a[0] = 7;
    a[j - 1] = 1;
    int r = a[0];
    return r;
}
```

```click
verifying "a_store_index_bound_and_disequality_keep_a_cached_element.c";

int32 read_first(int32 j) {
    requires 1 <= j;
    requires j <= 4;
    requires j != 1;
    ensures result == 7;
}
```

```expect
pass
```
