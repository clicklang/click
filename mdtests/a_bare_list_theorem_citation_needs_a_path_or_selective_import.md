# a bare list theorem citation needs a path or a selective import

`list` theorems follow the same rule as its functions: `append_left_identity`
here is not `list::append_left_identity`.

```click
theorem append_nil_by_bare_citation(xs: List<int32>) {
    ensures list::append(List<int32>::Nil, xs) == xs by {
        apply(append_left_identity(xs));
    }
}
```

```expect
fail: append_left_identity
```
