# an imported library name conflicts with a user definition

The negative twin of
[`an_unimported_library_name_is_free_for_a_user_definition.md`](an_unimported_library_name_is_free_for_a_user_definition.md).
After `import click::permutation;` the library's `permutation` is visible, so
a user `permutation` is a duplicate definition.

```click
import click::permutation;

predicate permutation(x: int32) {
    x == 1
}
```

```expect
fail: duplicate predicate definition `permutation`
```
