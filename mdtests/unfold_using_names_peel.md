# unfold takes no using list

Opening a range fold by the law its guards select is `peel`. The earlier
spelling, `unfold(f(args)) using { ... }`, is refused with the replacement.

```click
function icount(p: int32[], lo: int32, hi: int32) -> Integer {
    (lo..hi).fold(0, |acc, k| { acc + to_integer(p[k]) })
}

theorem icount_empty(p: int32[], lo: int32, hi: int32) {
    requires hi <= lo;
    ensures icount(p, lo, hi) == 0 by {
        unfold(icount(p, lo, hi)) using {
            hi <= lo;
        }
        normalize();
    }
}
```

```expect
fail: `unfold` takes no `using` list; write `peel(f(args)) using { ... }`
```
