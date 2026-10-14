# a short module path needs its module in scope

The negative twin of [`qualified_library_names.md`](qualified_library_names.md).
`integer::uint32_add_to_integer` names a declaration of `click::integer`,
which this file does not import, so the short path is refused and the message
names both fixes.

```click
theorem add_by_short_path(left: uint32, right: uint32) {
    requires to_integer(left) + to_integer(right) <= 4294967295;
    ensures to_integer(left + right) == to_integer(left) + to_integer(right)
        by apply(integer::uint32_add_to_integer(left, right));
}
```

```expect
fail: `integer::uint32_add_to_integer` names Click library module `click::integer`, which this file does not import; add `import click::integer;` or write `click::integer::uint32_add_to_integer`
```
