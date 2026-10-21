# peel using names its missing premise

A refused `peel ... using` in a pure theorem spells the listed premise that is
not a fact with the theorem's parameter names.

```c filename=peel_using_names_its_missing_premise.c
void unused(void) {}
```

```click
verifying "peel_using_names_its_missing_premise.c";

function tot(lo: int32, hi: int32) -> Integer {
    (lo..hi).fold(0, |acc, k| { acc + to_integer(k) })
}

theorem t(lo: int32, hi: int32) {
    ensures tot(lo, hi) == 0 by {
        peel(tot(lo, hi)) using { hi <= lo; };
    }
}
```

```expect
fail: `peel(tot(...)) using` requires an unavailable exact premise: hi <= lo
```
