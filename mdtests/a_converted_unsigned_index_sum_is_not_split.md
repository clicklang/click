# a converted unsigned index sum is not split into index plus constant

An `int32` scaled index is a 32-bit word: `a + (int32)w` is
`a + sext(w) * 4`. For a sum `w == u + c` that is `sext(u) * 4 + c * 4` only
when `u + c` does not wrap. A signed C addition never wraps (overflowing it
is undefined behavior, which the kernel refuses), but an unsigned addition
wraps by definition and converts to `int32` without complaint, so a word
such as `u + 2147483648` reaches a scaled index intact.

`offset_atoms_and_constant` took every `i + c` inside a scaled index apart:
the atom `u` and a shift of `c * 4`. For the store below that is the atom
`u` and a shift of `INT_MIN * 4` bytes. The run of cells that
`consumes a[0..8]` seeds then placed the store by the interval of `u` plus
that shift, a window lying wholly below the run, and kept every slot. So
`a[1]` kept its entry value across a store that writes it: with
`u == 2147483649`, `j` is `1`.

    j = (int32)(u + 2147483648u);    // u - 2^31 for u >= 2^31
    if (0 <= j < 8) a[j] = 6;        // judged to miss all of a[0..8]
    return a[1];                     // still 5?

The contract below verified;
`mdtests/a_bounded_converted_unsigned_index_sum_is_not_split.md` bounds `u`
to the values whose conversion is in range, and verified too. A scaled index
is now one atom whole; only a constant scaled index joins the constant
shift. The run then reads
the store's index as the word itself, whose interval the facts give
exactly, and the store may write `a[1]`.

`mdtests/signed_neighbour_indexes_stay_apart.md` is the positive next
door: a signed `a[i + 1]`, whose addition the step proves does not
overflow, still leaves `a[i]` in place.

```c filename=a_converted_unsigned_index_sum_is_not_split.c
int32 store_through_converted_sum(int32* a, uint32 u) {
    int32 j;
    j = (int32)(u + 2147483648u);
    if (j >= 0) {
        if (j < 8) {
            a[j] = 6;
        }
    }
    return a[1];
}
```

```click
verifying "a_converted_unsigned_index_sum_is_not_split.c";

int32 store_through_converted_sum(int32* a, uint32 u) {
    requires a[1] == 5;
    consumes a[0..8];
    ensures result == 5;
} by {
    execute();
    simp();
}
```

```expect
fail: unclosed goal
```
