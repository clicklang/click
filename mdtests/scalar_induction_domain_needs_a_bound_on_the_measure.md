# Signed `induct` needs a constant lower bound on the measure itself

`induct(n)` on an `int32` parameter reads its nonnegative domain from a held
bound `n >= c` (or `n > c`) with a constant `c >= 0` (or `c == -1` when
strict). It does not chain order facts: `0 <= m` and `m <= n` imply `0 <= n`,
but neither is a bound on `n`. Add `requires n >= 0;`, or prove `0 <= n` in
the theorem that applies this one.

```click
theorem domain_from_a_chain(n: int32, m: int32) {
    requires 0 <= m;
    requires m <= n;
    ensures n == n by {
        induct(n) as ih;
        normalize();
    }
}
```

```expect
fail: requires a proof that `n` is nonnegative
```
