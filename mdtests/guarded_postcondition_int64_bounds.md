# An `int64` guarded postcondition closes from its operands' bounds

Arithmetic search expands to ordinary proof steps, with the selected premises
stated explicitly in `close() using { ... }`.

The expansion proves `defined((old(st.total) + at(region(2).exit, got)))`
from the two operand bounds, `old(st.total) < 100` and
`at(region(2).exit, got) == 1`, then states and rewrites the consequent; the
expansion re-verifies (`src/surface/tests/expansion_tests.rs`). The explicit step on
its own, a widened operand, and the refusal when the bounds do not exclude
overflow are in [`int64_defined_from_bounds.md`](int64_defined_from_bounds.md)
and
[`int64_defined_bounds_do_not_exclude_overflow.md`](int64_defined_bounds_do_not_exclude_overflow.md).

```c filename=guarded_postcondition_int64_bounds.c
struct box {
    int v;
};

long bump(struct box* b) {
    return 1;
}

long caller(struct box* b) {
    long got;
    got = bump(b);
    return got;
}
```

```click
resource counted(b: struct box*) {
    field total: int64;
    owns *b;
}

verifying "guarded_postcondition_int64_bounds.c";

int64 bump(struct box* b) {
    owns st: counted(b);
    requires st.total < 100;
    ensures result == 1 or result == 2;
    ensures to_integer(st.total) == to_integer(old(st.total) + result);
} by {
    let { total: n } = unfold(st);
    let st = fold(counted(b), { total: n + 1 });
}

int64 caller(struct box* b) {
    owns st: counted(b);
    requires st.total < 100;
    ensures result == 1 implies to_integer(st.total) == to_integer(old(st.total) + 1);
} by {
    step();
    step(bump, { st: st });
}
```

```expect
pass
```
