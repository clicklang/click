# A store at another symbolic element keeps a cached one

Each function stores `7` at one element, then `1` at an element whose index
differs from it only by the contract's bounds, and reads the first back. No
proof body states the index disequality: the implicit tail proves it by
arithmetic before the second store, from the bounds alone (`1 <= j`,
`3 <= m`), in either store order, and for an automatic array as well as a
heap allocation.

```c filename=a_store_at_another_symbolic_element_keeps_a_cached_one.c
int at_parameter(int m, int j) {
    int *q = malloc(m * sizeof(int));
    if (q == 0) {
        return 0;
    }
    q[0] = 7;
    q[j] = 1;
    int r = q[0];
    free(q);
    return r;
}

int before_last(int m) {
    int *q = malloc(m * sizeof(int));
    if (q == 0) {
        return 0;
    }
    q[0] = 7;
    q[m - 2] = 1;
    int r = q[0];
    free(q);
    return r;
}

int read_last(int m) {
    int *q = malloc(m * sizeof(int));
    if (q == 0) {
        return 0;
    }
    q[m - 1] = 1;
    q[0] = 7;
    int r = q[m - 1];
    free(q);
    return r;
}

int on_the_stack(int m) {
    int a[8];
    a[0] = 7;
    a[m - 1] = 1;
    int r = a[0];
    return r;
}
```

```click
verifying "a_store_at_another_symbolic_element_keeps_a_cached_one.c";

int32 at_parameter(int32 m, int32 j) {
    requires 2 <= m;
    requires m <= 1000;
    requires 1 <= j;
    requires j < m;
    ensures result == 0 or result == 7;
}

int32 before_last(int32 m) {
    requires 3 <= m;
    requires m <= 1000;
    ensures result == 0 or result == 7;
}

int32 read_last(int32 m) {
    requires 2 <= m;
    requires m <= 1000;
    ensures result == 0 or result == 1;
}

int32 on_the_stack(int32 m) {
    requires 2 <= m;
    requires m <= 8;
    ensures result == 7;
}
```

```expect
pass
```
