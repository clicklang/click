# simp is written without parentheses anywhere

`by simp;` drops the parentheses, and so may a `simp` step inside a block:
`simp;` is `simp();`, with or without a `using` list.

```click
theorem bare_simp_steps(x: int32) {
    requires 0 <= x;
    ensures 0 <= x by {
        simp;
    }
    ensures 0 <= x by {
        have 0 <= x by { simp using { 0 <= x; } }
        simp();
    }
}
```

```expect
pass
```
