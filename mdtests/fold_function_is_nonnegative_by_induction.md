# a range fold over a symbolic range is proved by ordinary induction

This is the point of stating the fold laws over the function application. The
theorem is about a whole symbolic range, and its proof is the existing
`induct(hi)` over a nonnegative int32 parameter: the base case is the
empty-range equation, and the step case relates `marks(lo, hi)` to
`marks(lo, hi - 1)` — the very term the induction hypothesis speaks about,
because both sides of the append equation are the same function.

Nothing here retypes the fold, and no fold law is applied by name. The two
`peel` steps refresh the goal through the equation they open, so
the step case closes with the induction hypothesis and one bound on the cell
the last iteration adds.

```click
import click::integer;

function marks(lo: int32, hi: int32) -> Integer {
    (lo..hi).fold(0, |acc, k| { acc + to_integer(if k == 0 { 1 } else { 0 }) })
}

theorem marks_nonnegative(lo: int32, hi: int32) {
    requires 0 <= lo;
    requires 0 <= hi;
    ensures 0 <= marks(lo, hi) by {
        induct(hi) as ih;
        if hi <= lo {
            peel(marks(lo, hi)) using {
                hi <= lo;
            };
            solve();
        } else {
            have lo < hi;
            have 0 <= to_integer(hi - 1) by { solve() using { 0 <= lo; lo < hi; }; }
            have to_integer(hi - 1) < to_integer(hi) by { solve() using { 0 <= lo; lo < hi; }; }
            apply(ih(hi - 1)) using {
                0 <= to_integer(hi - 1);
                to_integer(hi - 1) < to_integer(hi);
                0 <= lo;
            };
            have to_integer(lo) <= to_integer(hi - 1) by { solve() using { 0 <= lo; lo < hi; }; }
            have to_integer(hi - 1) < 2147483647 by { solve() using { 0 <= lo; lo < hi; }; }
            peel(marks(lo, hi)) using {
                to_integer(lo) <= to_integer(hi - 1);
                to_integer(hi - 1) < 2147483647;
            };
            have 0 <= to_integer(if to_integer(hi - 1) == 0 { 1 } else { 0 });
            solve() using {
                0 <= marks(lo, hi - 1);
                0 <= to_integer(if to_integer(hi - 1) == 0 { 1 } else { 0 });
            };
        }
    }
}
```

```expect
pass
```
