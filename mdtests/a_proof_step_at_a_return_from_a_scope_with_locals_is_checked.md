# a proof step at a return from a scope with locals is still checked

The proof steps a `return` inside a block accepts after `execute()` are
checked as at any return: a `fold` that claims a value the cell does not hold
is refused.

```c filename=a_proof_step_at_a_return_from_a_scope_with_locals_is_checked.c
int32 read_or_zero(int32 *p) {
    if (*p != 0) {
        int32 y = *p;
        return y;
    }
    return 0;
}
```

```click
resource cell(q: int32*) {
    field v: int32;
    owns *q;
    fact *q == v;
}

verifying "a_proof_step_at_a_return_from_a_scope_with_locals_is_checked.c";

int32 read_or_zero(int32* p) {
    consumes before: cell(p);
    produces after: cell(p);
    ensures after.v == old(before.v);
} by {
    let {} = unfold(before);
    execute();
    let after = fold(cell(p), { v: old(before.v) + 1 }, {});
}
```

```expect
fail: fold
```
