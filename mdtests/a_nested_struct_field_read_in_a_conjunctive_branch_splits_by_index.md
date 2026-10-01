# A nested struct-field read in a conjunctive branch splits by its index

The nested-struct variant of
`mdtests/a_struct_field_read_in_a_conjunctive_branch_splits_by_index.md`:
`items[x].at.y` reads at `x * 12 + 8`, which only the cells at `8` and `20`
share a residue with modulo the 12-byte stride.

```c filename=a_nested_struct_field_read_in_a_conjunctive_branch_splits_by_index.c
struct point {
    int32 x;
    int32 y;
};

struct labeled {
    int32 label;
    struct point at;
};

int32 f(int32 x) {
    struct labeled items[2] = {{1, {2, 3}}, {4, {5, 6}}};
    int32 r = 0;
    if (0 <= x && x < 2) {
        r = items[x].at.y;
    }
    return r;
}
```

```click
verifying "a_nested_struct_field_read_in_a_conjunctive_branch_splits_by_index.c";

int32 f(int32 x) {
    ensures result == 0 or result == 3 or result == 6;
} by {
    execute();
    simp();
}
```

```expect
pass
```
