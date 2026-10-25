# A `-> Integer` function with an `if` body unfolds

The body of a `-> Integer` function is an Integer position, and an `if`
there has Integer branches. `unfold` opens its defining equation: with a
literal condition the conditional is its branch, so `pick(n, true)` is
`n + 1`; with a symbolic one the unfolded goal keeps the conditional, and
the proof splits on its condition.

```click
function pick(n: Integer, c: bool) -> Integer { if c { n + 1 } else { n } }

theorem pick_true(n: Integer) {
    ensures pick(n, true) == n + 1 by {
        unfold(pick(n, true));
        normalize();
    }
}

theorem pick_is_at_least_its_argument(n: Integer, c: bool) {
    ensures pick(n, c) >= n by {
        unfold(pick(n, c));
        if c {
            have (if c { n + 1 } else { n }) == n + 1 by solve();
            solve();
        } else {
            have (if c { n + 1 } else { n }) == n by solve();
            solve();
        }
    }
}
```

```expect
pass
```
