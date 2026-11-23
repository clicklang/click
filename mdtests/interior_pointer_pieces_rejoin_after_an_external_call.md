# interior-pointer pieces rejoin after an external call

The external `wr` owns one cell at each of `p` and `q`. Calling it on `x + i`
and `x + j` carves `x[i..i + 1]` and `x[j..j + 1]` out of the caller's
`owns x[0..4]`, and the call returns them spelled over their own bases as
`(x + i)[0..1]` and `(x + j)[0..1]`. Restated over `x` they abut the carved
residues, so the pieces rejoin into the `owns x[0..4]` the caller gives back.
The proof holds `x[0..i]` apart during the call so both argument cells are
reserved from the suffix. When the call returns, the proof unfolds the prefix
and returns ownership of the whole array.

```c filename=interior_pointer_pieces_rejoin_after_an_external_call.c
extern int32 wr(int32* p, int32* q);

int32 caller(int32* x, int32 i, int32 j) {
    int32 r;
    r = wr(x + i, x + j);
    return r;
}
```

```click
verifying "interior_pointer_pieces_rejoin_after_an_external_call.c";

resource retained_prefix(x: int32*, end: int32) { owns x[0..end]; }

extern int32 wr(int32* p, int32* q) {
    owns p[0..1];
    owns q[0..1];
    ensures result == 1;
}

int32 caller(int32* x, int32 i, int32 j) {
    requires 0 <= i;
    requires to_integer(i + 1) <= to_integer(j);
    requires j < 4;
    owns x[0..4];
    ensures result == 1;
} by {
    have i < 4;
    have 0 <= j;

    fold(retained_prefix(x, i));
    step();
    step();
    unfold(retained_prefix(x, i));
    step();
    step();
    solve();
}
```

```expect
pass
```
