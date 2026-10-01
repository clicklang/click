# A bounded symbolic read of a static const local table has one of its values

The function-local `static const` form of
`mdtests/a_bounded_symbolic_read_of_a_const_global_table_has_one_of_its_values.md`.

```c filename=a_bounded_symbolic_read_of_a_static_const_local_table_has_one_of_its_values.c
int32 g(int32 x) {
    static const int32 table[4] = {1, 2, 3, 4};
    int32 r = 0;
    if (0 <= x && x < 4) {
        r = table[x];
    }
    return r;
}
```

```click
verifying "a_bounded_symbolic_read_of_a_static_const_local_table_has_one_of_its_values.c";

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
