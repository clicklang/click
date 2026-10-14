# A returned fold uses a theorem applied after return

A theorem applied after `execute()` reaches the function's exit is a
checked fact on the returning path, exactly as a `have` there is. A later
fold of a produced resource may rely on its conclusion.

```c filename=pick.c
int32 pick(int32* p, int32 x) {
    *p = x;
    return x;
}
```

```click
spec enum Shape { Leaf, Pair(int32, int32) }
function first(s: Shape) -> int32 {
    match s {
        Shape::Leaf => 0,
        Shape::Pair(a, b) => a,
    }
}
theorem first_pair(a: int32, b: int32) {
    ensures first(Shape::Pair(a, b)) == a by { unfold(first(Shape::Pair(a, b))); normalize(); }
}
resource Cell(p: int32*) {
    field model: int32;
    owns p[0..1];
    fact p[0] == model;
}
verifying "pick.c";
int32 pick(int32* p, int32 x) {
    consumes p[0..1];
    produces c: Cell(p);
    ensures c.model == first(Shape::Pair(x, 3));
} by {
    execute();
    apply(first_pair(x, 3));
    let c = fold(Cell(p), { model: x });
    simp();
}
```

```expect
pass
```
