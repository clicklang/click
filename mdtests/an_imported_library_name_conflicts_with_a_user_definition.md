# an imported library name conflicts with a user definition

The negative twin of
[`an_unimported_library_name_is_free_for_a_user_definition.md`](an_unimported_library_name_is_free_for_a_user_definition.md).
`import click::permutation::{permutation};` brings the library's
`permutation` into scope by its bare name, so a user `permutation` clashes
with it. A module import alone, `import click::permutation;`, brings only
the path `permutation::permutation`, and leaves the bare name free.

```click
import click::permutation::{permutation};

predicate permutation(x: int32) {
    x == 1
}
```

```expect
fail: `permutation` is imported from `click::permutation` and also declared in this file
```
