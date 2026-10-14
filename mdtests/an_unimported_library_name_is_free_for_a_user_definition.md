# a name in an unimported library module is free for a user definition

`click::permutation` declares `permutation`, but this file does not import
it, so its own `permutation` is the only one it sees. The negative twin is
[`an_imported_library_name_conflicts_with_a_user_definition.md`](an_imported_library_name_conflicts_with_a_user_definition.md).

```click
predicate permutation(x: int32) {
    x == 1
}

theorem one_is_a_permutation() {
    ensures permutation(1) by {
        unfold(permutation);
        simp();
    }
}
```

```expect
pass
```
