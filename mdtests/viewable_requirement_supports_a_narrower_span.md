# A viewability requirement supports a narrower range

A stated `viewable(v[lo..hi])` requirement carries the guards for its byte
span. The proof establishes the smaller interval's endpoint order, proves
containment, then restricts viewability to that interval.

```click
theorem narrow_viewable_requirement(v: int32[], lo: int32, hi: int32) {
    requires 0 <= lo;
    requires lo < hi;
    requires hi >= 0 and viewable(v[lo..hi]);
    ensures viewable(v[lo..hi - 1]) by {
        have 0 < hi by { close() using { 0 <= lo; lo < hi; }; }
        have defined(hi - 1) by { close() using { 0 < hi; }; }
        have to_integer(lo) <= to_integer(hi - 1) by {
            close() using { 0 < hi; lo < hi; };
        }
        have to_integer(hi - 1) <= to_integer(hi) by {
            close() using { 0 < hi; };
        }
        have contains(memory(v[lo..hi]), memory(v[lo..hi - 1])) by {
            apply(click::separation::contains_subrange(v, lo, hi, lo, hi - 1));
        }
        apply(click::separation::viewable_restrict(memory(v[lo..hi]), memory(v[lo..hi - 1])));
    }
}
```

```expect
pass
```
