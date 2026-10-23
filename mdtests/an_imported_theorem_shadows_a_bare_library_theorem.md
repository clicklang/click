# An imported theorem shadows a bare library theorem

The imported module declares its own `integer_multiply_add`, which proves
only `a == a`. A bare citation names it, as a local theorem of the name
is named, so the library theorem `click::integer`'s does not close this goal.
Before, a local theorem shadowed the library's while an imported one did not:
the citation silently applied the library theorem.

```click
import "an_imported_theorem_shadows_a_bare_library_theorem_module.click";
import click::integer;

theorem uses(a: Integer, b: Integer, c: Integer) {
    ensures (a + b) * c == a * c + b * c by {
        apply(integer_multiply_add(a, b, c));
    }
}
```

```expect
fail: ended with its goal still open
```
