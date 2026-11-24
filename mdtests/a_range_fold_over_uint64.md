# A range fold over uint64

A range with `uint64` endpoints ranges over `uint64` values, and its item has
that type. Ordinary `unfold` opens its empty and append laws. The append law
needs an endpoint below the largest `uint64`, where its successor does not
wrap; normal obligations check this condition.

```click
function total(lo: uint64, hi: uint64) -> Integer {
    (lo..hi).fold(0, |acc, k| { acc + to_integer(k) })
}

function upto(hi: uint64) -> Integer {
    (0..hi).fold(0, |acc, k| { acc + to_integer(k) })
}

theorem empty(n: uint64) {
    ensures total(n, n) == 0 by {
        have n <= n;
        unfold(total(n, n));
        close();
    }
}

theorem step(lo: uint64, hi: uint64) {
    requires lo <= hi;
    requires hi < 18446744073709551615u64;
    ensures total(lo, hi + 1u64) == total(lo, hi) + to_integer(hi) by {
        unfold(total(lo, hi + 1u64));
        close();
    }
}

theorem step_from_zero(hi: uint64) {
    requires hi < 18446744073709551615u64;
    ensures upto(hi + 1u64) == upto(hi) + to_integer(hi) by {
        unfold(upto(hi + 1u64));
        close();
    }
}
```

```expect
pass
```
