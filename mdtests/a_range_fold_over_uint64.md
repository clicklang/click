# A range fold over uint64

A range fold took `int32` or `Integer` endpoints. A function describing
code that indexes by `size_t` or `usize` then had to convert the index at
every use. A range whose endpoints are `uint64` ranges over `uint64`
values, and its item `k` has that type.

`peel` opens the same two laws as for an `int32` range, with unsigned
order: the empty range gives the initial value, and one more element adds
the body at the old end. The append law needs `hi` below the largest
`uint64`, where `hi + 1` does not wrap.

`upto` writes its start as the literal `0`, which is that `uint64`.

`a_uint64_range_fold_step_needs_its_guards.md` leaves a guard out.

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
        peel(total(n, n)) using { n <= n; }
        normalize();
    }
}

theorem step(lo: uint64, hi: uint64) {
    requires lo <= hi;
    requires hi < 18446744073709551615u64;
    ensures total(lo, hi + 1u64) == total(lo, hi) + to_integer(hi) by {
        peel(total(lo, hi + 1u64)) using { lo <= hi; hi < 18446744073709551615u64; }
        simp();
    }
}

theorem step_from_zero(hi: uint64) {
    requires hi < 18446744073709551615u64;
    ensures upto(hi + 1u64) == upto(hi) + to_integer(hi) by {
        peel(upto(hi + 1u64)) using { 0u64 <= hi; hi < 18446744073709551615u64; }
        simp();
    }
}
```

```expect
pass
```
