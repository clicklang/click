# a bounded converted unsigned index sum is not split either

`mdtests/a_converted_unsigned_index_sum_is_not_split.md` with `u` bounded to
`[2^31, 2^31 + 7]`, so every conversion below is in range and the program has
no implementation-defined value at all: `j == u - 2^31` names each element of
`a[0..8]` once. The split read the store as the atom `u`, whose interval is
`[INT_MIN, INT_MIN + 7]` as a signed word, plus `INT_MIN` elements, which is
`2^32` elements below the store's real address; the run kept `a[1]`, and the
contract verified.

```c filename=a_bounded_converted_unsigned_index_sum_is_not_split.c
int32 store_through_bounded_converted_sum(int32* a, uint32 u) {
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
verifying "a_bounded_converted_unsigned_index_sum_is_not_split.c";

int32 store_through_bounded_converted_sum(int32* a, uint32 u) {
    requires u >= 2147483648u32;
    requires u <= 2147483655u32;
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
