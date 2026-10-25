# a 32-bit cell read at the other signedness is not its stored number

The refusal beside
`a_32_bit_cell_read_at_the_other_signedness_is_its_sign_cast.md`:
`4294967295u` stored and read through `int *` is `-1`, not the stored number.

```c filename=a_32_bit_cell_read_at_the_other_signedness_is_not_its_stored_number.c
int unsigned_stored_read_signed(void) {
    unsigned cells[1];
    int *s;
    cells[0] = 4294967295u;
    s = (int *)(void *)cells;
    return s[0];
}
```

```click
verifying "a_32_bit_cell_read_at_the_other_signedness_is_not_its_stored_number.c";

int unsigned_stored_read_signed() { ensures result == 4294967295 by auto(); }
```

```expect
fail: `ensures result == 4294967295` failed for `unsigned_stored_read_signed.ensures_0`
```
