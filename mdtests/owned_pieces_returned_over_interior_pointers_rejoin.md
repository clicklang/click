# owned pieces returned over interior pointers rejoin

A call on `x + i` and `x + j` carves `owns x[i..i + 1]` and
`owns x[j..j + 1]` out of the caller's `owns x[0..4]` and returns them as
`owns (x + i)[0..1]` and `owns (x + j)[0..1]`. The returned pieces are spelled
over their own bases, but each sits an exact number of elements from `x`, so
restated over `x` they abut the carved residues `x[0..i]`, `x[i + 1..j]`, and
`x[j + 1..4]`, and the five pieces rejoin into the `owns x[0..4]` the caller
must give back. A constant displacement such as `x + 1` rejoins the same way.

```c filename=owned_pieces_returned_over_interior_pointers_rejoin.c
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

int32 constant_caller(int32* x) {
    int32 r;
    r = wr(x + 1, x + 2);
    return r;
}
```

```click
verifying "owned_pieces_returned_over_interior_pointers_rejoin.c";

int32 wr(int32* p, int32* q) {
    owns p[0..1];
    owns q[0..1];
    ensures result == 1 by auto;
}

int32 caller(int32* x, int32 i, int32 j) {
    requires 0 <= i;
    requires i < 4;
    requires i + 1 <= j;
    requires 0 <= j;
    requires j < 4;
    owns x[0..4];
    ensures result == 1 by auto;
}

int32 constant_caller(int32* x) {
    owns x[0..4];
    ensures result == 1 by auto;
}
```

```expect
pass
```
