# Discovery of a generic library theorem

Both discovered and explicit applications accept an Integer element type.

```click
import click::list;

theorem lengths(xs: List<Integer>, ys: List<Integer>) {
    ensures list::length(list::append(xs, ys)) == nat::add(list::length(xs), list::length(ys)) by {
        solve() using {};
    }
    ensures list::length(list::append(xs, ys)) == nat::add(list::length(xs), list::length(ys)) by {
        apply(list::length_append(xs, ys));
    }
}
```

```expect
pass
```
