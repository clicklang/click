# A struct-field read in a conjunctive branch claimed without a value is refused

The negative of
`mdtests/a_struct_field_read_in_a_conjunctive_branch_splits_by_index.md`: in
the case `x == 1` the read is `items[1].y`, which is `4`, so a claim that
leaves `4` out is refused there.

```c filename=a_struct_field_read_in_a_conjunctive_branch_claimed_without_a_value_is_refused.c
struct point {
    int32 x;
    int32 y;
};

int32 f(int32 x) {
    struct point items[2] = {{1, 2}, {3, 4}};
    int32 r = 0;
    if (0 <= x && x < 2) {
        r = items[x].y;
    }
    return r;
}
```

```click
verifying "a_struct_field_read_in_a_conjunctive_branch_claimed_without_a_value_is_refused.c";

int32 f(int32 x) {
    ensures result == 0 or result == 2;
} by {
    execute();
    simp();
}
```

```expect
fail: case: [0 <= x, x < 2, x == 0 is false]
```
