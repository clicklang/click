# A stated store search fact keeps the heap cell

The program of
`mdtests/a_store_search_miss_names_the_store_and_the_fact_for_a_heap_read.md`,
with the fact its refusal names stated before `statement(3)`. `solve` proves
`((m - 1) as int32) != 0` from `1 <= m` and `m != 1`, and the store keeps
`q[0]`.

```c filename=a_stated_store_search_fact_keeps_the_heap_cell.c
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
verifying "a_stated_store_search_fact_keeps_the_heap_cell.c";

int32 read_first(int32 m) {
    requires 1 <= m;
    requires m <= 1000;
    requires m != 1;
    ensures result == 0 or result == 7 by {
        step(); step();
        if q == 0 {
            step_until(function.exit);
        } else {
            step_until(statement(3));
            have not (let integer_value: Integer = to_integer(((m - 1) as int32)); integer_value) == 0 by solve();
            step_until(function.exit);
        }
    }
}
```

```expect
pass
```
