# a cited library theorem is available after its module's import

The positive twin of
[`a_cited_library_theorem_needs_its_module_import.md`](a_cited_library_theorem_needs_its_module_import.md).

```click
import click::machine_integer;

theorem chain(a: uint32, b: uint32, c: uint32) {
    requires a < b;
    requires b < c;
    ensures a < c by apply(uint32_less_than_transitive(a, b, c));
}
```

```expect
pass
```
