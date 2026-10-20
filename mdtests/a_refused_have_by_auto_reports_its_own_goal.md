# A refused have by auto reports its own goal

A `have ... by auto()` that `auto` cannot prove inside a theorem's
`ensures ... by` block is refused at its `auto()`, with the `have`'s goal,
not declined to the enclosing claim. The `have` is false: nothing bounds
`word & 1`.

```c filename=a_refused_have_by_auto_reports_its_own_goal.c
void unused(void) {}
```

```click
verifying "a_refused_have_by_auto_reports_its_own_goal.c";

theorem have_goal(word: uint64, base: uint64) {
    requires to_integer(word) == to_integer(base);
    ensures to_integer(word) == to_integer(base) by {
        have (word & 1) == 0 by auto();
        assumption();
    }
}
```

```expect
fail: `auto` could not prove `(word & 1) == 0`
```
