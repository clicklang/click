# byte count of two merged branches matches the C count

Two `if` statements each add one to a counter when a byte equals `x`.
After `execute()` merges both branches, the result is a sum of conditional
terms, and `simp()` matches it against the unfolded `byte_count` fold of
the `uint8` prelude. Deciding the overflow of the second increment needs the
signed interval of the first conditional, and the byte comparisons are
resolved through equality facts anchored on the loaded bytes. This catches a
byte-slice count whose merged conditional sum no longer simplifies to the
prelude definition.

```c filename=byte_count_of_two_merged_branches_matches_the_c_count.c
int32 count_byte2(uint8 p[], uint8 x) {
    int32 count;
    count = 0;
    if (p[0] == x) {
        count = count + 1;
    }
    if (p[1] == x) {
        count = count + 1;
    }
    return count;
}
```

```click
verifying "byte_count_of_two_merged_branches_matches_the_c_count.c";

int32 count_byte2(uint8 p[], uint8 x) {
    views p[0..2];
    ensures result == byte_count(p, 0, 2, x) by {
        execute();
        unfold(byte_count(p, 0, 2, x));
        simp();
    }
}
```

```expect
pass
```
