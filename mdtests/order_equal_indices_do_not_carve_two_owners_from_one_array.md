# order-equal indices do not carve two owners from one array

`i <= j` and `j <= i` make `x + i` and `x + j` one cell, so the call would
hand `wr` two owners of it. The call is refused for overlapping owners.
Admitting it would let `wr` prove `result == 1` from their separation where
the C returns 2.

```c filename=order_equal_indices_do_not_carve_two_owners_from_one_array.c
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
verifying "order_equal_indices_do_not_carve_two_owners_from_one_array.c";

int32 wr(int32* p, int32* q) {
    owns p[0..1];
    owns q[0..1];
    ensures result == 1 by auto();
}

int32 caller(int32* x, int32 i, int32 j) {
    requires 0 <= i;
    requires i < 4;
    requires 0 <= j;
    requires j < 4;
    requires i <= j;
    requires j <= i;
    owns x[0..4];
    ensures result == 1 by auto();
}
```

```expect
fail: overlapping owned memory resource facts `owns x[i]` and `owns x[j]`
```
