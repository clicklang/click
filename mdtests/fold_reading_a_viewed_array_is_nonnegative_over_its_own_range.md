# a range fold over its own viewed range is proved by ordinary induction

`mdtests/fold_reading_an_array_is_nonnegative_over_its_own_range.md` proves this
theorem with the range stated as `requires hi >= 0 and viewable(v[lo..hi]);`.
That conjunction was not a style choice: a bare `requires viewable(...)` did not
compile in a theorem, so the range had to ride inside a proposition. `views
v[lo..hi];` states the same hypothesis directly, and this file is the same proof
with that one clause changed. The original stays as the regression for the
spelling that still exists.

Two lines disappear with the conjunction. The hypothesis premise is now the
range itself, so `apply(ih(hi - 1))` names it as `viewable(v[lo..hi - 1])` —
the fact form, which is how a `views` premise is named in a `using` list —
instead of rebuilding `hi - 1 >= 0 and viewable(v[lo..hi - 1])` with `known()`.

Both proofs use `array_fold_induction_bounds` to establish their scalar order and
span facts. The theorem carries `hi <= 1073741823`, which with `0 <= lo` bounds the range's
element count by the largest count a four-byte range can have and still be a
valid 32-bit byte span. The induction hypothesis owes that bound at the
smaller endpoint like every other precondition, and the narrowing step needs the
count itself pinned to `0..=1073741823`.

```click
import "array_fold_induction_bounds.click";
import click::integer;

function unmarked(v: int32[], lo: int32, hi: int32) -> Integer {
    (lo..hi).fold(0, |acc, k| { acc + to_integer(if v[k] == 0 { 1 } else { 0 }) })
}

theorem unmarked_nonnegative(v: int32[], lo: int32, hi: int32) {
    views v[lo..hi];
    requires 0 <= lo;
    requires 0 <= hi;
    requires hi <= 1073741823;
    ensures 0 <= unmarked(v, lo, hi) by {
        let ih = induct(hi);
        if hi <= lo {
            unfold(unmarked(v, lo, hi));
            solve();
        } else {
            have lo < hi;
            apply(array_fold_induction_bounds(lo, hi));
            have viewable(v[lo..hi - 1]);
            apply(ih(hi - 1));
            unfold(unmarked(v, lo, hi));
            have 0 <= (if v[hi - 1] == 0 { 1 } else { 0 });
            solve() using { 0 <= unmarked(v, lo, hi - 1); to_integer(0) <= to_integer(if v[hi - 1] == 0 { 1 } else { 0 }); };
        }
    }
}
```

```expect
pass
```
