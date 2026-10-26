# Construct guarded and matched memory resources

Explicit folds check the selected body using current memory and proposed fields.
Unfold consumes the instance; it does not leave an open handle.

```c filename=resource_conditional_construction.c
void set(int32* p, int32 value) { *p = value; }
void nullable(int32* p, int32 value) { if (p != 0) *p = value; }
void empty(int32* p) { }
```

```click
verifying "resource_conditional_construction.c";
spec enum Maybe<T> { None, Some(T) }

resource cell(p: int32*) {
    field model: Maybe<int32>;
    match model {
        Maybe::None => { fact p == 0; },
        Maybe::Some(value) => { owns p[0..1]; fact p[0] == value; },
    }
}

resource guarded(p: int32*) {
    field value: int32;
    if p != 0 { owns p[0..1]; fact p[0] == value; }
}

void set(int32* p, int32 value) {
    consumes p[0..1];
    produces c: cell(p);
    ensures c.model == Maybe<int32>::Some(value);
} by {
    step_until(function.exit);
    let c = fold(cell(p), { model: Maybe<int32>::Some(value) });
    solve();
}

void empty(int32* p) {
    requires p == 0;
    produces c: cell(p);
    ensures c.model == Maybe<int32>::None;
} by {
    let c = fold(cell(p), { model: Maybe<int32>::None });
}

void nullable(int32* p, int32 value) {
    owns c: guarded(p);
    ensures c.value == value;
} by {
    if p == 0 {
        unfold(c);
        step_until(function.exit);
        let c = fold(guarded(p), { value: value });
        solve();
    } else {
        unfold(c);
        step_until(function.exit);
        let c = fold(guarded(p), { value: value });
        solve();
    }
}
```

```expect
pass
```
