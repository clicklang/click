# a cited library theorem needs its module's import

The negative twin of [`click_library_import.md`](click_library_import.md).
`integer::multiply_add` is declared in `click::integer`, which
is not implicit. A proof that cites it by its short path without
`import click::integer;` is refused before any proof runs, and the
message names the import to add.

```click
theorem distribute(a: Integer, b: Integer, c: Integer) {
    ensures (a + b) * c == a * c + b * c by apply(integer::multiply_add(a, b, c));
}
```

```expect
fail: `integer::multiply_add` names Click library module `click::integer`, which this file does not import; add `import click::integer;` or write `click::integer::multiply_add`
```
