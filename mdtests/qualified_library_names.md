# Click library declarations have qualified names

A library declaration's full name is its module path and its name. A full
`click::` path needs no import: `click::integer::integer_multiply_add`
brings `click::integer` itself. A module in scope, implicit like
`click::list` or imported, is also named by its last segment, so
`list::append` names the same function as `click::list::append`.

```click
theorem append_nil_by_paths(xs: List<int32>) {
    ensures list::append(List<int32>::Nil, xs) == xs by {
        apply(click::list::append_left_identity(xs));
    }
}

theorem distribute_by_full_path(a: Integer, b: Integer, c: Integer) {
    ensures (a + b) * c == a * c + b * c
        by apply(click::integer::integer_multiply_add(a, b, c));
}
```

```expect
pass
```
