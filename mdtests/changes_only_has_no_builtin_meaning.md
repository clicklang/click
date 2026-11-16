# changes_only is not a built-in transition proposition

```click
theorem no_builtin(before: Integer, after: Integer) {
    ensures changes_only(before, after);
}
```

```expect
fail: unknown predicate `changes_only`
```
