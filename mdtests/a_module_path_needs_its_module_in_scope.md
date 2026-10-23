# a short module path needs its module in scope

The negative twin of [`qualified_library_names.md`](qualified_library_names.md).
`integer::integer_multiply_add` names a declaration of `click::integer`,
which this file does not import, so the short path is refused and the message
names both fixes.

```click
theorem distribute_by_short_path(a: Integer, b: Integer, c: Integer) {
    ensures (a + b) * c == a * c + b * c
        by apply(integer::integer_multiply_add(a, b, c));
}
```

```expect
fail: `integer::integer_multiply_add` names Click library module `click::integer`, which this file does not import; add `import click::integer;` or write `click::integer::integer_multiply_add`
```
