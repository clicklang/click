# owned pieces that may not abut do not rejoin

The caller holds `owns x[0..i + 1]` and `owns x[j..j + 1]`, and the call on
`x + j` returns the second piece as `owns (x + j)[0..1]`. Restated over `x`
it starts at `j`, and `i + 1 <= j` does not make that the first piece's end
`i + 1`: under `i + 1 < j` the cells between are held by no one. Rejoining
the pieces into `owns x[0..j + 1]` would produce cells the caller never held,
so the produced range is missing.

```c filename=owned_pieces_that_may_not_abut_do_not_rejoin.c
void wr(int32* p) {
    *p = 1;
}

void caller(int32* x, int32 i, int32 j) {
    wr(x + j);
}
```

```click
verifying "owned_pieces_that_may_not_abut_do_not_rejoin.c";

void wr(int32* p) {
    owns p[0..1];
}

void caller(int32* x, int32 i, int32 j) {
    requires 0 <= i;
    requires i + 1 <= j;
    requires j < 4;
    consumes x[0..(i + 1)];
    consumes x[j..(j + 1)];
    produces x[0..(j + 1)] by auto;
}
```

```expect
fail: missing resource fact `owns x[0..(j + 1)]`
```
