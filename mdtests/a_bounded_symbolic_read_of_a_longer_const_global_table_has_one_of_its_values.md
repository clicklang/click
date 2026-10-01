# A bounded symbolic read of a longer const global table has one of its values

The eight-entry form of
`mdtests/a_bounded_symbolic_read_of_a_const_global_table_has_one_of_its_values.md`.

```c filename=a_bounded_symbolic_read_of_a_longer_const_global_table_has_one_of_its_values.c
const int32 table[8] = {5, 9, 2, 7, 3, 8, 6, 4};

int32 g(int32 x) {
    int32 r = 0;
    if (0 <= x && x < 8) {
        r = table[x];
    }
    return r;
}
```

```click
verifying "a_bounded_symbolic_read_of_a_longer_const_global_table_has_one_of_its_values.c";

int32 g(int32 x) {
    ensures result >= 0;
    ensures result <= 9;
} by {
    execute();
    simp();
}
```

```expect
pass
```
