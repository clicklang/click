# `unfold(f(args))` applies a function that shares an instance's name

The instance `cell2` and the pure function `cell2` share a name. A bare
`unfold(cell2)` opens the instance; `unfold(cell2(pv))` applies the function,
as its arguments say. Before, the application was read as the instance and
refused with "expected `)`, got `(`".

```c filename=unfold_applies_a_function_that_shares_an.c
int32 get(int32* p) { return *p; }
```

```click
verifying "unfold_applies_a_function_that_shares_an.c";

resource cell(p: int32*) {
    field v: int32;
    owns p[0..1];
    fact p[0] == v;
}

function cell2(x: int32) -> int32 { x + 1 }

int32 get(int32* p) {
    owns cell2: cell(p);
    ensures result + 1 == cell2(cell2.v);
} by {
    let { v: pv } = unfold(cell2);
    execute();
    let cell2 = fold(cell(p), { v: pv });
    unfold(cell2(pv));
    simp();
}
```

```expect
pass
```
