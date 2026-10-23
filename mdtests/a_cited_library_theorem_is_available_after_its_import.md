# a cited library theorem is available after its module's import

The positive twin of
[`a_cited_library_theorem_needs_its_module_import.md`](a_cited_library_theorem_needs_its_module_import.md).

```click
import click::integer;

theorem distribute(a: Integer, b: Integer, c: Integer) {
    ensures (a + b) * c == a * c + b * c by apply(integer::multiply_add(a, b, c));
}
```

```expect
pass
```
