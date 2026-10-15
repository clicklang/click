# Generic proofs are checked without concrete clients

```click
theorem reflexive<T>(x: T) {
    ensures x == x by normalize();
}

theorem via_generic<T>(x: T) {
    ensures x == x by apply(reflexive(x));
}

theorem independent<T, U>(x: T, y: U) {
    ensures x == x by apply(reflexive(x));
    ensures y == y by apply(reflexive(y));
}

theorem list_law<T>(xs: List<T>, ys: List<T>, value: T) {
    ensures list::contains(list::append(xs, ys), value)
        == if list::contains(xs, value) { true } else { list::contains(ys, value) } by {
        apply(list::contains_append(xs, ys, value));
    }
}

theorem nested<T>(xs: List<List<T>>) {
    ensures list::append(xs, List<List<T>>::Nil) == xs by {
        apply(list::append_right_identity(xs));
    }
}
```

```expect
pass
```
