# Click library declarations have qualified names

A library declaration's full name is its module path and its name. A full
`click::` path needs no import: `click::integer::uint32_add_to_integer`
brings `click::integer` itself. A module in scope, implicit like
`click::list` or imported, is also named by its last segment, so
`list::append` names the same function as `click::list::append`.

```click
theorem append_nil_by_paths(xs: List<int32>) {
    ensures list::append(List<int32>::Nil, xs) == xs by {
        apply(click::list::append_left_identity(xs));
    }
}

theorem add_by_full_path(left: uint32, right: uint32) {
    requires to_integer(left) + to_integer(right) <= 4294967295;
    ensures to_integer(left + right) == to_integer(left) + to_integer(right)
        by apply(click::integer::uint32_add_to_integer(left, right));
}
```

```expect
pass
```
