# An imported theorem shadows a bare library theorem

The imported module declares its own `int32_less_equal_to_integer`, which
proves only `left <= right`. A bare citation names it, as a local theorem
of the name is named, so the library theorem `click::integer`'s does not
close this goal. Before, a local theorem shadowed the library's while an
imported one did not: the citation silently applied the library theorem.

```click
import "an_imported_theorem_shadows_a_bare_library_theorem_module.click";
import click::integer;

theorem uses(a: int32, b: int32) {
    requires a <= b;
    ensures to_integer(a) <= to_integer(b) by {
        apply(int32_less_equal_to_integer(a, b));
    }
}
```

```expect
fail: ended with its goal still open
```
