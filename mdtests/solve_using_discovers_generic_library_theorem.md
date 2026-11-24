# Discovery of a generic library theorem

Both discovered and explicit applications accept an Integer element type.

```click quick-solve
import click::list;

theorem lengths(xs: List<Integer>, ys: List<Integer>) {
    ensures list::length(list::append(xs, ys)) == nat::add(list::length(xs), list::length(ys)) by {
        close() using {};
    }
    ensures list::length(list::append(xs, ys)) == nat::add(list::length(xs), list::length(ys)) by {
        apply(list::length_append(xs, ys));
    }
}
```

```expect
pass
```
