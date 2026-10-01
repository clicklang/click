# A struct-field read in a conjunctive branch splits by its index

`items[x].y` reads at byte offset `x * 8 + 4`. The cells initialized at
`0`, `4`, `8` and `12` were each a path case of the read, and the cases at
`4` and `12` had no Click spelling, so `execute()` could not split them. The
offset differs from `0` and `8` modulo the 8-byte stride, so those cells are
now distinct from it without a case, and `x * 8 + 4 == 12` is `x == 1`. The
read splits into `x == 0`, `x == 1` and the rest, exactly as a scalar
`items[x]` does. As for the scalar read, the remaining case is not yet
refuted from `0 <= x < 2`
(`bugs/symbolic-array-read-values-are-not-bounded.md`), so this claims only
that execution reaches the end.

```c filename=a_struct_field_read_in_a_conjunctive_branch_splits_by_index.c
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
verifying "a_struct_field_read_in_a_conjunctive_branch_splits_by_index.c";

int32 f(int32 x) {
    ensures result == result;
} by {
    execute();
    simp();
}
```

```expect
pass
```
