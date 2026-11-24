# The former changes_only spelling is an ordinary function name

```click
function changes_only(x: Integer) -> Integer { x }

theorem identity(x: Integer) {
    ensures changes_only(x) == x by {
        unfold(changes_only(x));
        close();
    }
}
```

```expect
pass
```
