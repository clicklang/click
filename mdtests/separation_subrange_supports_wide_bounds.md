# Subrange containment retains unsigned 64-bit bounds

```click
import click::separation;

theorem wide(p: int32*, lo: uint64, hi: uint64, a: uint64, b: uint64) {
    requires lo <= a;
    requires a <= b;
    requires b <= hi;
    ensures contains(memory(p[lo..hi]), memory(p[a..b])) by {
        apply(separation::subrange(p, lo, hi, a, b)) using {
            lo <= a; a <= b; b <= hi;
        };
    }
}
```

```expect
pass
```
