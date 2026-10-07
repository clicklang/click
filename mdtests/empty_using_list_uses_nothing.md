# an empty using list uses nothing

`using { }` is accepted wherever a list is, and means the tactic uses no
premises. That differs from leaving `using` off: `simp()` would find the
precondition below in the context, while `simp() using { }` may not use it.

```click
theorem empty_using_uses_nothing(x: int32) {
    requires 0 <= x;
    ensures 0 <= x by {
        simp() using { }
    }
}
```

```expect
fail: `simp() using` could not prove the current goal from only its listed premises
```
