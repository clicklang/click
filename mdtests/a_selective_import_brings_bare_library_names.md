# a selective import brings bare library names

`import click::list::{append, length};` brings `append` and `length` into
scope by their bare names; every other library name still needs its path,
here `list::append_left_identity`.

```click
import click::list::{append, length};

theorem append_nil_by_bare_names(xs: List<int32>) {
    ensures append(List<int32>::Nil, xs) == xs by {
        apply(list::append_left_identity(xs));
    }
}
```

```expect
pass
```
