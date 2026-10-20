# a return from a scope with locals accepts proof steps at the return

A `return` inside a block ends the block's automatic locals after the return
statement itself. A proof step after `execute()` at that return, such as the
`fold` that produces a contract's resource, still finds the return statement
that completed the path.

```c filename=a_return_from_a_scope_with_locals_accepts_return_proof_steps.c
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

verifying "a_return_from_a_scope_with_locals_accepts_return_proof_steps.c";

int32 read_or_zero(int32* p) {
    consumes before: cell(p);
    produces after: cell(p);
    ensures after.v == old(before.v);
} by {
    let {} = unfold(before);
    execute();
    let after = fold(cell(p), { v: old(before.v) }, {});
}
```

```expect
pass
```
