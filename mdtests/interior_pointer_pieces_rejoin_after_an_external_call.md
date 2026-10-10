# interior-pointer pieces rejoin after an external call

The external `wr` owns one cell at each of `p` and `q`. Calling it on `x + i`
and `x + j` carves `x[i..i + 1]` and `x[j..j + 1]` out of the caller's
`owns x[0..4]`, and the call returns them spelled over their own bases as
`(x + i)[0..1]` and `(x + j)[0..1]`. Restated over `x` they abut the carved
residues, so the pieces rejoin into the `owns x[0..4]` the caller gives back.
The indices are symbolic and the callee is unverified; this catches a rejoin
that cannot
rebase a returned piece onto `x` or match the two pieces' offsets.

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

extern int32 wr(int32* p, int32* q) {
    owns p[0..1];
    owns q[0..1];
    ensures result == 1;
}

int32 caller(int32* x, int32 i, int32 j) {
    requires 0 <= i;
    requires i + 1 <= j;
    requires j < 4;
    owns x[0..4];
    ensures result == 1;
} by {
    step();
    step();
    step();
    simp();
}
```

```expect
pass
```
