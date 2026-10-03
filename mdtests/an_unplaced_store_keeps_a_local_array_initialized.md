# an unplaced store keeps a local array initialized

`loc[u] = 7` under `0 <= u < 2` may write either element of a fully written
automatic array, so the store forgets both cached values. It used to forget
that they were ever written too: automatic storage had no initialization
record apart from its cells, so the read of `loc[0]` after the store was
refused as a read of uninitialized storage. A store only ever initializes
bytes; the memory's initialization record now keeps the forgotten cells'
bytes, and the read is an ordinary load of an initialized element whose value
is the one the facts leave open: `7` if `u == 0`, the old `5` otherwise.

So `result >= 5` and the disjunction both verify, and `result == 5` (below,
in `mdtests/an_unplaced_store_leaves_a_local_element_value_open.md`) is an
ordinary unclosed goal rather than undefined behavior.

```c filename=an_unplaced_store_keeps_a_local_array_initialized.c
int32 may_hit_either(int32 u) {
    int32 loc[2];
    loc[0] = 5;
    loc[1] = 5;
    loc[u] = 7;
    return loc[0];
}

int32 old_or_new(int32 u) {
    int32 loc[2];
    loc[0] = 5;
    loc[1] = 5;
    loc[u] = 7;
    return loc[0];
}

int32 any_element(int32 u, int32 v) {
    int32 loc[2];
    loc[0] = 5;
    loc[1] = 6;
    loc[u] = 7;
    return loc[v];
}
```

```click
verifying "an_unplaced_store_keeps_a_local_array_initialized.c";

int32 may_hit_either(int32 u) {
    requires 0 <= u;
    requires u < 2;
    ensures result >= 5;
} by {
    execute();
    simp();
}

int32 old_or_new(int32 u) {
    requires 0 <= u;
    requires u < 2;
    ensures result == 5 or result == 7;
} by {
    execute();
    simp();
}

int32 any_element(int32 u, int32 v) {
    requires 0 <= u;
    requires u < 2;
    requires 0 <= v;
    requires v < 2;
    ensures result == result;
} by {
    execute();
    simp();
}
```

```expect
pass
```
