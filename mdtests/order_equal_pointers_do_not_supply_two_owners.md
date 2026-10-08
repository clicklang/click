# order-equal pointers do not supply two owners

`requires x <= y; requires y <= x;` makes `x` and `y` one address, so the
caller holds one cell. `wr` owns two cells, and its entry partition reads its
two `owns` clauses as disjoint memory, so it frames the store through `q` away
from the load through `p` and proves `result == 1`. At `p == q` the C returns
2. The partition is sound only because every call must reserve each owned
requirement out of what the caller still holds: once `owns x[0..1]` backs `p`,
nothing is left to back `q`, however `y` is related to `x`.

A contract such as `wr` stays admissible even when its own `requires` would
force `p == q` by order facts: its precondition is then unsatisfiable, and
this refusal is what keeps it so. `order_equal_indices_do_not_carve_two_owners_from_one_array.md`
is the same boundary inside one array, and
`a_return_cannot_produce_two_owners_of_order_equal_pointers.md` is the same
boundary at a return.

```c filename=order_equal_pointers_do_not_supply_two_owners.c
int32 wr(int32* p, int32* q) {
    *p = 1;
    *q = 2;
    return *p;
}

int32 caller(int32* x, int32* y) {
    int32 r;
    r = wr(x, y);
    return r;
}
```

```click
verifying "order_equal_pointers_do_not_supply_two_owners.c";

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
fail: missing resource fact `owns y[0]`
```
