# order bounds place a store off a constant element

`loc[u] = 7` under `1 <= u` cannot write `loc[0]`: the two element indices
`0` and `u` are strictly ordered, so they are different words. Memory
resolution told the two addresses apart only from a disequality (`u != 0`)
or a constant, never from the order bounds that settle the disequality, so
the store dropped `loc[0]` of an automatic array, which then read as
uninitialized storage: the call was refused as undefined behavior. (Through
a pointer parameter whose run of cells `consumes a[0..2]` seeds, the run
already placed the store by the interval of `u` and kept `a[0]`.)

The offset comparison now also reads the constant bounds recorded on the
symbolic index, one keyed lookup: an index whose bounds exclude the other,
constant index is a different word, so the offsets differ. Only the
disequality follows.

`mdtests/an_unordered_store_index_may_write_a_constant_element.md` is the
negative next door: under `0 <= u` the store may write `a[0]`.

```c filename=order_bounds_place_a_store_off_a_constant_element.c
int32 below(int32 u) {
    int32 loc[2];
    loc[0] = 5;
    loc[1] = 5;
    loc[u] = 7;
    return loc[0];
}

int32 above(int32 u) {
    int32 loc[3];
    loc[0] = 5;
    loc[1] = 5;
    loc[2] = 5;
    loc[u] = 7;
    return loc[2];
}

int32 through_parameter(int32* a, int32 u) {
    a[0] = 5;
    a[1] = 5;
    a[u] = 7;
    return a[0];
}
```

```click
verifying "order_bounds_place_a_store_off_a_constant_element.c";

int32 below(int32 u) {
    requires 1 <= u;
    requires u < 2;
    ensures result == 5;
} by {
    execute();
    simp();
}

int32 above(int32 u) {
    requires 0 <= u;
    requires u < 2;
    ensures result == 5;
} by {
    execute();
    simp();
}

int32 through_parameter(int32* a, int32 u) {
    requires 1 <= u;
    requires u < 2;
    consumes a[0..2];
    ensures result == 5;
} by {
    execute();
    simp();
}
```

```expect
pass
```
