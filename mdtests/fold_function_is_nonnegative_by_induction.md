# a range fold over a symbolic range is proved by ordinary induction

This is the point of stating the fold laws over the function application. The
theorem is about a whole symbolic range, and its proof is the existing
`induct(hi)` over a nonnegative int32 parameter: the base case is the
empty-range equation, and the step case relates `marks(lo, hi)` to
`marks(lo, hi - 1)` — the very term the induction hypothesis speaks about,
because both sides of the append equation are the same function.

Nothing here retypes the fold, and no fold law is applied by name. The two
`unfold` steps refresh the goal through the equation they open, so
the step case closes with the induction hypothesis and one bound on the cell
the last iteration adds. The last item is stated as `int32`, preserving the
fold body's native comparison when its index is substituted.

```click
import click::integer;

function marks(lo: int32, hi: int32) -> Integer {
    (lo..hi).fold(0, |acc, k| { acc + to_integer(if k == 0 { 1 } else { 0 }) })
}

theorem marks_nonnegative(lo: int32, hi: int32) {
    requires 0 <= lo;
    requires 0 <= hi;
    ensures 0 <= marks(lo, hi) by {
        let ih = induct(hi);
        if hi <= lo {
            unfold(marks(lo, hi));
            close();
        } else {
            have lo < hi;
            have 0 <= to_integer(hi - 1) by { close() using { 0 <= lo; lo < hi; }; }
            have to_integer(hi - 1) < to_integer(hi) by { close() using { 0 <= lo; lo < hi; }; }
            apply(ih(hi - 1));
            have to_integer(lo) <= to_integer(hi - 1) by { close() using { 0 <= lo; lo < hi; }; }
            have to_integer(hi - 1) < 2147483647 by { close() using { 0 <= lo; lo < hi; }; }
            unfold(marks(lo, hi));
            have 0 <= to_integer(if (hi - 1) as int32 == 0 { 1 } else { 0 });
            close() using {
                0 <= marks(lo, hi - 1);
                0 <= to_integer(if (hi - 1) as int32 == 0 { 1 } else { 0 });
            };
        }
    }
}
```

```expect
pass
```
