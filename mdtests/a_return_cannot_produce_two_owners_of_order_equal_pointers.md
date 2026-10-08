# a return cannot produce two owners of order-equal pointers

`dup`'s contract receives one cell and promises two owners back, at `p` and
at `q`, where its `requires` make `p` and `q` one address. If its return were
admitted, a caller holding one cell could leave the call holding two owners of
it and pass them to a function whose entry partition frames one away from the
other, proving `result == 1` where the C returns 2. The return is checked the
way a call is: once `owns p[0..1]` is produced, nothing remains to produce
`owns q[0..1]`.

```c filename=a_return_cannot_produce_two_owners_of_order_equal_pointers.c
int32 dup(int32* p, int32* q) {
    return 0;
}

int32 wr(int32* p, int32* q) {
    *p = 1;
    *q = 2;
    return *p;
}

int32 caller(int32* x, int32* y) {
    int32 ignored;
    int32 r;
    ignored = dup(x, y);
    r = wr(x, y);
    return r;
}
```

```click
verifying "a_return_cannot_produce_two_owners_of_order_equal_pointers.c";

int32 dup(int32* p, int32* q) {
    requires p <= q;
    requires q <= p;
    consumes p[0..1];
    produces p[0..1];
    produces q[0..1];
}

int32 wr(int32* p, int32* q) {
    owns p[0..1];
    owns q[0..1];
    ensures result == 1 by auto;
}

int32 caller(int32* x, int32* y) {
    requires x <= y;
    requires y <= x;
    owns x[0..1];
    ensures result == 1 by auto;
}
```

```expect
fail: missing resource fact `owns q[0]`
```
