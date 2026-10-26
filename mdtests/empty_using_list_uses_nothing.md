# an empty using list uses nothing

`using { }` is accepted wherever a list is, and means the tactic uses no
premises. That differs from leaving `using` off: `solve()` would find the
precondition below in the context, while `solve() using { }` may not use it.

```click
theorem empty_using_uses_nothing(x: int32) {
    requires 0 <= x;
    ensures 0 <= x by {
        solve() using { };
    }
}
```

```expect
fail: `solve() using` could not prove the current goal from only its listed premises
```
