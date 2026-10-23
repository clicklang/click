# a cited library theorem needs its module's import

The negative twin of [`click_library_import.md`](click_library_import.md).
`integer_multiply_add` is declared in `click::integer`, which
is not implicit. A proof that cites it by name without
`import click::integer;` is refused before any proof runs, and the
message names the import to add.

```click
theorem distribute(a: Integer, b: Integer, c: Integer) {
    ensures (a + b) * c == a * c + b * c by apply(integer_multiply_add(a, b, c));
}
```

```expect
fail: unknown theorem `integer_multiply_add`; it is declared in Click library module `click::integer`, so add `import click::integer;`
```
