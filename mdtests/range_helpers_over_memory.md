# Range helpers over memory reads

`.all`, `.any`, and `.fold` bind a range item whose memory read is guarded by
range membership, so `viewable(p[lo..hi])` makes `p[k]` safe in the body; a
symbolic `.any` is proved with `witness` on the range item name.

```c filename=range_helpers_over_memory.c
int32 bounded_by(int32 p[], int32 lo, int32 hi, int32 x) {
    return 0;
}

int32 has_in_first_three(int32 p[], int32 x) {
    return 0;
}

int32 first_in_range(int32 p[], int32 lo, int32 hi) {
    return p[lo];
}

int32 zeros_with_needle(int32 p[], int32 lo, int32 hi, int32 needle) {
    return 0;
}
```

```click
verifying "range_helpers_over_memory.c";

function range_sum(p: int32[], lo: int32, hi: int32) -> int32 {
    (lo..hi).fold(0, |acc, k| { acc + p[k] })
}

int32 bounded_by(int32 p[], int32 lo, int32 hi, int32 x) {
    requires 0 <= lo and lo <= hi;
    requires viewable(p[lo..hi]);
    requires (lo..hi).all(|k| { p[k] <= x });
    ensures (lo..hi).all(|k| { p[k] <= x }) by auto();
}

int32 has_in_first_three(int32 p[], int32 x) {
    requires viewable(p[0..3]);
    requires p[1] == x;
    ensures (0..3).any(|k| { p[k] == x }) by {
        execute();
        witness { k: 1 };
        simp();
    }
}

int32 first_in_range(int32 p[], int32 lo, int32 hi) {
    requires 0 <= lo and lo < hi;
    views p[lo..hi];
    ensures found: (lo..hi).any(|k| { p[k] == result }) by {
        execute();
        witness { k: lo };
        simp();
    }
}

int32 zeros_with_needle(int32 p[], int32 lo, int32 hi, int32 needle) {
    requires 0 <= lo and lo <= hi;
    requires viewable(p[lo..hi]);
    requires (lo..hi).all(|k| { p[k] == 0 });
    requires (lo..hi).any(|k| { p[k] == needle });
    ensures range_sum(p, lo, hi) == range_sum(p, lo, hi) by auto();
}
```

```expect
pass
```
