# a call refusal names the cell an earlier argument reserved

With `i < j` and no upper bound on `j`, the call reserves
`owns x[i..(i + 1)]` for `p` first, which carves the caller's `owns x[0..4]`
into `x[0..i]` and `x[(i + 1)..4]`. Neither piece need cover `x[j..(j + 1)]`,
since `j` may be 4 or more, so the owner `q` needs is missing and the call is
refused.

The refusal's note used to compare the missing range with the caller's
context before the reservation, which says nothing about why the call was
refused. It now names the reservation and compares against what remained
after it. (When the two cells are known to be one, as with `i <= j` and
`j <= i`, the call is refused earlier for overlapping owners instead; see
`order_equal_indices_do_not_carve_two_owners_from_one_array.md`.)

```c filename=call_refusal_names_the_cell_an_earlier_argument_reserved.c
int32 wr(int32* p, int32* q) {
    *p = 1;
    *q = 2;
    return *p;
}

int32 caller(int32* x, int32 i, int32 j) {
    int32 r;
    r = wr(x + i, x + j);
    return r;
}
```

```click
verifying "call_refusal_names_the_cell_an_earlier_argument_reserved.c";

int32 wr(int32* p, int32* q) {
    owns p[0..1];
    owns q[0..1];
    ensures result == 1 by auto;
}

int32 caller(int32* x, int32 i, int32 j) {
    requires 0 <= i;
    requires i < 4;
    requires i < j;
    owns x[0..4];
    ensures result == 1 by auto;
}
```

```expect
fail: after reserving [`owns x[i]`] for an earlier requirement of this call
```
