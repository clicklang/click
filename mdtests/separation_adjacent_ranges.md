# Adjacent half-open ranges are separate without inspecting memory

```click
import click::separation;

theorem narrow(p: int32*, lo: int32, mid: int32, hi: int32) {
    requires lo <= mid;
    requires mid <= hi;
    ensures separate(memory(p[lo..mid]), memory(p[mid..hi])) by {
        apply(separation::separate_adjacent_ranges(p, lo, mid, hi)) using { lo <= mid; mid <= hi; };
    }
}

theorem wide(p: uint8*, lo: uint64, mid: uint64, hi: uint64) {
    requires lo <= mid;
    requires mid <= hi;
    ensures separate(memory(p[lo..mid]), memory(p[mid..hi])) by {
        apply(separation::separate_adjacent_ranges(p, lo, mid, hi)) using { lo <= mid; mid <= hi; };
    }
}

theorem empty(p: int32*, i: int32) {
    ensures separate(memory(p[i..i]), memory(p[i..i])) by {
        have i <= i by { normalize(); }
        apply(separation::separate_adjacent_ranges(p, i, i, i)) using { i <= i; };
    }
}
```

```expect
pass
```
