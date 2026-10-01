# a signed and an unsigned byte read are two values

`s[i]` and `u[i]` read the same byte, once as `signed char` and once as
`unsigned char`. A byte holding `0xFF` is `-1` through `s` and `255` through
`u`, so the two reads are equal only when the byte is below `0x80`, and
`result == 1` is false.

That claim was **provable**. A load term named the address and the snapshot
but not what was read there, so both reads became one term, and `a == b` was
`v == v`. The term now carries the read's kind — its width, and below four
bytes its signedness (`LoadKind`) — and a signed and an unsigned byte read
are two terms.

`a_byte_read_is_not_the_int32_read_at_its_address.md` is the same hole across
widths, and `reads_of_one_kind_at_one_address_stay_equal.md` keeps the reads
that do agree on their kind equal. The note on the C in
`a_byte_store_inside_a_wide_cell_is_not_framed.md` applies to the byte view.

```c filename=a_signed_and_an_unsigned_byte_read_are_two_values.c
int read_both(signed char* s, int i) {
    unsigned char* u;
    int a;
    int b;
    u = (unsigned char*)(void*) s;
    a = s[i];
    b = u[i];
    return a == b;
}
```

```click
verifying "a_signed_and_an_unsigned_byte_read_are_two_values.c";

int read_both(signed char* s, int i) {
    requires i >= 0;
    requires i < 4;
    views s[0..4];
    ensures result == 1;
} by {
    execute();
    simp();
}
```

```expect
fail: `ensures result == 1` failed for `read_both.ensures_0`
```
