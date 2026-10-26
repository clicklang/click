# 64-bit `solve() using` reads orders written either way round

`solve() using` proves a `uint64` or `int64` goal through its Integer
observations, carrying each listed order to Integer by a bridge theorem that
states it as `left < right` or `left <= right`. A premise written the other
way round, `i > 0`, is restated that way round by `assumption` first, and a
goal written the other way round, `i - 1 >= 0`, is proved as `0 <= i - 1` and
closed from it. A difference's range is shown from the operands' own type
ranges where no premise bounds them: `i - 1` is defined under `0 < i`
because `i` is at most `INT64_MAX`.

```click
theorem predecessor_nonnegative(i: int64) {
    requires i > 0;

    ensures 0 <= i - 1 by {
        solve() using {
            i > 0;
        };
    }
}

theorem predecessor_below(i: int64, n: int64) {
    requires i <= n;
    requires i > 0;

    ensures n >= i - 1 by {
        solve() using {
            i <= n;
            i > 0;
        };
    }
}

theorem unsigned_predecessor_below(i: uint64, n: uint64) {
    requires n >= i;
    requires i > 0;

    ensures i - 1 <= n by {
        solve() using {
            n >= i;
            i > 0;
        };
    }
}
```

```expect
pass
```
