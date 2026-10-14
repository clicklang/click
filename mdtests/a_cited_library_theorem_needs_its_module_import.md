# a cited library theorem needs its module's import

The negative twin of [`click_library_import.md`](click_library_import.md).
`uint32_less_than_transitive` is declared in `click::machine_integer`, which
is not implicit. A proof that cites it by name without
`import click::machine_integer;` is refused before any proof runs, and the
message names the import to add.

```click
theorem chain(a: uint32, b: uint32, c: uint32) {
    requires a < b;
    requires b < c;
    ensures a < c by apply(uint32_less_than_transitive(a, b, c));
}
```

```expect
fail: unknown theorem `uint32_less_than_transitive`; it is declared in Click library module `click::machine_integer`, so add `import click::machine_integer;`
```
