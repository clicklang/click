# Unfold rejects a using list

Ordinary `unfold` uses facts from the current proof context and emits normal
obligations for missing guards. It does not take a tactic-specific premise list.

```click
function icount(p: int32[], lo: int32, hi: int32) -> Integer {
    (lo..hi).fold(0, |acc, k| { acc + to_integer(p[k]) })
}

theorem icount_empty(p: int32[], lo: int32, hi: int32) {
    requires hi <= lo;
    ensures icount(p, lo, hi) == 0 by {
        unfold(icount(p, lo, hi)) using {
            hi <= lo;
        };
        close();
    }
}
```

```expect
fail: `unfold` takes no `using` list; its guards are ordinary proof obligations
```
