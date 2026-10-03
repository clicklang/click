# A bounded symbolic read of a const global table has one of its values

A `const` table's initializer is its contents at every function entry.
The first element is stored as a constant run over the table, and the later
elements are cells stored over it. The read `values[x]` splits on those cells,
`x == 1` through `x == 3`, and the case past them reads the run's one live
slot. That read needs the index on the slot, and the interval `0 <= x <= 3`
alone did not place it there. Each end of the interval now moves past the
values a fact excludes, so `x != 1`, `x != 2` and `x != 3` leave `[0, 0]`, and
the case reads `1`.
`mdtests/a_bounded_symbolic_read_of_a_const_global_table_claimed_above_its_first_value_is_refused.md`
is the negative.

```c filename=a_bounded_symbolic_read_of_a_const_global_table_has_one_of_its_values.c
const int32 values[4] = {1, 2, 3, 4};

int32 g(int32 x) {
    int32 r = 0;
    if (0 <= x && x < 4) {
        r = values[x];
    }
    return r;
}
```

```click
verifying "a_bounded_symbolic_read_of_a_const_global_table_has_one_of_its_values.c";

int32 g(int32 x) {
    ensures result >= 0;
    ensures result <= 4;
} by {
    execute();
    simp();
}
```

```expect
pass
```
