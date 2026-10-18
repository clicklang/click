# A literal constructor field takes the field's type

A literal written as a constructor's argument is a value of that field's
type, as a C initializer's is: `2` in `Seq<int64>::Cons(2, ...)` is an
`int64`. Before, it lowered at the narrowest width holding it, an `int32`,
so the constructor denoted no `Seq<int64>` value and a true claim comparing
it with `same(2)` was refused as lowering to no path.

```click
spec enum Seq<T> {
    Nil,
    Cons(T, Seq<T>),
}

function same(x: int64) -> Seq<int64> {
    Seq::Cons(x, Seq::Nil)
}

theorem literal_fields() {
    ensures same(2) == Seq<int64>::Cons(2, Seq<int64>::Nil) by {
        unfold(same(2));
        simp();
    }
    ensures same(-2) == Seq<int64>::Cons(-2, Seq<int64>::Nil) by {
        unfold(same(-2));
        simp();
    }
}
```

```expect
pass
```
