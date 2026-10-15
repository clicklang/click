# Reflexivity does not unfold symbolic algebraic terms

```click
theorem opaque_list_call_reflexive<T>(xs: List<T>, ys: List<T>) {
    ensures list::append(xs, ys) == list::append(xs, ys) by normalize();
}

theorem symbolic_list_match_reflexive<T>(xs: List<T>, ys: List<T>) {
    ensures (match xs {
        List::Nil => ys,
        List::Cons(head, tail) => list::append(tail, ys),
    }) == (match xs {
        List::Nil => ys,
        List::Cons(head, tail) => list::append(tail, ys),
    }) by { normalize(); }
}
```

```expect
pass
```
