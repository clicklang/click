# A constant constructor field takes the field's type

A constant built only from unsuffixed literals, such as `3 - 1`, is the
literal it denotes when written as a constructor's argument. So it takes the
field's type, as `2` does. Before, it lowered as an `int32`, the constructor
denoted no `Seq<int64>` value, and a true claim was refused as lowering to
no path.

```click
spec enum Seq<T> {
    Nil,
    Cons(T, Seq<T>),
}

theorem constant_fields() {
    ensures Seq<int64>::Cons(3 - 1, Seq<int64>::Nil) == Seq<int64>::Cons(2, Seq<int64>::Nil) by {
        solve();
    }
    ensures Seq<int64>::Cons(2 * 3 + -7, Seq<int64>::Nil) == Seq<int64>::Cons(-1, Seq<int64>::Nil) by {
        solve();
    }
}
```

```expect
pass
```
