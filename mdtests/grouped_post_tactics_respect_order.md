# Grouped post-execution tactics respect source order

`solve()` closes only claims provable at its position. A fact established by a
later `have` does not retroactively affect that earlier `solve()` tactic.

```c filename=grouped_post_order.c
int32 identity(int32 x) {
    return x;
}
```

```click
verifying "grouped_post_order.c";

int32 identity(int32 x) {
    ensures exists (k: int32) { k + 1 == result + 1 };
} by {
    execute();
    solve();
    have exists (k: int32) { k + 1 == result + 1 } by {
        witness { k: result };
        solve();
    }
}
```

```expect
fail: unclosed goal: exists
```
