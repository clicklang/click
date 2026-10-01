# A struct-field read one past a conjunctive bound is refused

The negative of
`mdtests/a_struct_field_read_in_a_conjunctive_branch_splits_by_index.md`.
Under `0 <= x && x < 3`, `x == 2` reads past `items`, and `execute()` is
refused for the element bound it could not show.

```c filename=a_struct_field_read_one_past_a_conjunctive_bound_is_refused.c
struct point {
    int32 x;
    int32 y;
};

int32 f(int32 x) {
    struct point items[2] = {{1, 2}, {3, 4}};
    int32 r = 0;
    if (0 <= x && x < 3) {
        r = items[x].y;
    }
    return r;
}
```

```click
verifying "a_struct_field_read_one_past_a_conjunctive_bound_is_refused.c";

int32 f(int32 x) {
    ensures result == result;
} by {
    execute();
    simp();
}
```

```expect
fail: missing prerequisite (array subobject index must be at least 0 and less than 2): could not show `x >= 0 && x < 2`
```
