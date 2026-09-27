# signed neighbour indexes stay apart

The positive beside `mdtests/a_converted_unsigned_index_sum_is_not_split.md`.
A scaled index `i + 1` is no longer taken apart into `i` plus one element, but
a signed C index needs no such split: the step proves `i + 1` does not
overflow, and the facts bound the word `i + 1` itself. A store at `a[i + 1]`
leaves `a[i]` in place both in a range seeded from a constant start and in
one anchored at `i`.

```c filename=signed_neighbour_indexes_stay_apart.c
int32 store_both(int32* a, int32 i) {
    a[i] = 1;
    a[i + 1] = 2;
    return a[i];
}

int32 store_next(int32* a, int32 i) {
    int32 x;
    x = a[i];
    a[i + 1] = x + 1;
    return a[i] - x;
}

int32 store_next_in_anchored_range(int32* a, int32 i) {
    int32 x;
    x = a[i];
    a[i + 1] = x + 1;
    return a[i] - x;
}
```

```click
verifying "signed_neighbour_indexes_stay_apart.c";

int32 store_both(int32* a, int32 i) {
    requires 0 <= i;
    requires i < 7;
    consumes a[0..8];
    ensures result == 1;
} by {
    execute();
    simp();
}

int32 store_next(int32* a, int32 i) {
    requires 0 <= i;
    requires i < 7;
    requires a[i] < 100;
    requires a[i] > -100;
    consumes a[0..8];
    ensures result == 0;
} by {
    execute();
    simp();
}

int32 store_next_in_anchored_range(int32* a, int32 i) {
    requires 0 <= i;
    requires i < 1000;
    requires a[i] < 100;
    requires a[i] > -100;
    consumes a[i..(i + 2)];
    ensures result == 0;
} by {
    execute();
    simp();
}
```

```expect
pass
```
