# a range fold over its own viewable range is proved by ordinary induction

`mdtests/fold_reading_an_array_is_nonnegative_by_induction.md` proves the same
theorem with the viewable range pinned to a separate parameter `n` that the
induction never moves. That was a workaround, and this is the shape it was
working around: the range ends at `hi`, the endpoint `induct(hi)` descends on,
so `apply(ih(hi - 1))` demands `viewable(v[lo..hi - 1])` as an exactly available
fact.

That fact is now provable, so the workaround is not needed. `induct(hi)` gives
an induction hypothesis guarded by the theorem's own `requires` at the smaller
endpoint; `have viewable(v[lo..hi - 1]);` narrows the theorem's
own range to that endpoint, against the order facts established by the shared
`array_fold_induction_bounds` theorem. Induction application checks both
conjuncts of the substituted requirement.

The theorem also carries `hi <= 1073741823`, which with `0 <= lo` bounds the
range's element count by the largest count a four-byte range can have and still
be a valid 32-bit byte span. The induction hypothesis needs that bound at the
smaller endpoint like every other precondition, and the narrowing step needs the
count itself pinned to `0..=1073741823`, which the shared theorem supplies. This is a
real precondition of the shape, not bookkeeping: a range of `1 << 30` `int32`
elements has a byte span of `1 << 32`, which wraps to `0`.

```click
import "array_fold_induction_bounds.click";
import click::integer;

function unmarked(v: int32[], lo: int32, hi: int32) -> Integer {
    (lo..hi).fold(0, |acc, k| { acc + to_integer(if v[k] == 0 { 1 } else { 0 }) })
}

theorem unmarked_nonnegative(v: int32[], lo: int32, hi: int32) {
    requires 0 <= lo;
    requires 0 <= hi;
    requires hi <= 1073741823;
    requires hi >= 0 and viewable(v[lo..hi]);
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
