# stdlib list length rejects successor

```click
theorem invalid<T>(xs: List<T>, ys: List<T>) {
    ensures list::length(list::append(xs, ys)) == Nat::Succ(nat::add(list::length(xs), list::length(ys))) by {
        apply(list::length_append(xs, ys));
        normalize();
    }
}
```

```expect
fail: invalid.ensures_0
```

