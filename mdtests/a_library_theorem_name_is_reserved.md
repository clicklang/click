# a library theorem name is reserved even without its module's import

Built-in tactics apply Click library theorems by name whatever a file
imports, so a file theorem may not take a library theorem's name, even one
from a module the file does not import. Predicates and functions of an
unimported module are free instead; see
[`an_unimported_library_name_is_free_for_a_user_definition.md`](an_unimported_library_name_is_free_for_a_user_definition.md).

```click
theorem uint32_less_than_transitive(a: uint32) {
    ensures a == a by simp;
}
```

```expect
fail: theorem `uint32_less_than_transitive` has the name of a Click library theorem, which built-in tactics apply; rename it
```
