# A machine-integer fact is held only in Integer form, so exact tactics cannot use it

Soundness: incomplete. Valid proof steps are refused; nothing false verifies.

A `have` of a `uint64` comparison or equality over subtraction is recorded in
its Integer form: `n - 1u64 == (n - r) - 1u64` becomes
`to_integer(n) - 1 == to_integer(n) - to_integer(r) - 1`, and `n - r < n`
becomes `to_integer(n) - to_integer(r) < to_integer(n)`. Tactics that match a
fact against machine terms exactly then cannot use it:

- `rewrite(P)` with that equality reports that it does not occur in a goal
  that contains its left side as written;
- `instantiate(F, v) using { P; }` with that comparison as the guard reports
  that the guard "does not follow from the listed evidence", though the
  evidence is the guard itself.

This blocks ordinary slice proofs: relating an iterator's cursor offset
(`len - remaining`) to an index, or instantiating a slice-wide `forall` at
that offset. It surfaced proving that `enumerate` yields `xs[i]`
(`design/charon-trial/enumerate` states a weaker claim for this reason).

## Reproduction

`rw.c`:

```c
unsigned int pick(unsigned int *xs, unsigned long n, unsigned long r) {
    return xs[n - 1];
}
```

```click
verifying "rw.c";

uint32 pick(uint32* xs, uint64 n, uint64 r) {
    requires r == 0u64 and n != 0u64;
    views xs[0..n];
    ensures result == xs[(n - r) - 1u64];
} by {
    have n - 1u64 == (n - r) - 1u64 by {
        rewrite(r == 0u64);
        solve();
    }
    have xs[n - 1u64] == xs[(n - r) - 1u64] by {
        rewrite(n - 1u64 == (n - r) - 1u64);
        solve();
    }
}
```

```text
`rewrite` equality does not occur in the current goal
equality: to_integer(n) - 1 == to_integer(n) - to_integer(r) - 1
goal: xs[(n - 1u64)] == xs[((n - r) - 1u64)]
```

`inst.c`:

```c
unsigned int at(unsigned int *xs, unsigned long n, unsigned long r) {
    return xs[n - r];
}
```

```click
verifying "inst.c";

uint32 at(uint32* xs, uint64 n, uint64 r) {
    requires 0u64 < r and r <= n;
    requires forall (k: uint64) { k < n implies xs[k] <= 100u32 };
    views xs[0..n];
    ensures result <= 100u32;
} by {
    have n - r < n;
    have xs[n - r] <= 100u32 by {
        instantiate(forall (k: uint64) { k < n implies xs[k] <= 100u32 }, n - r) using {
            n - r < n;
        };
    }
}
```

```text
`instantiate` failed
instantiated premise `n - r < n` does not follow from the listed evidence
```

Without `using`, `instantiate` reports the guard missing as an exact fact.

## Acceptance criteria

- Both reproductions verify as written.
- A wrong rewrite (`n - 2u64 == (n - r) - 1u64`) and a guard that does not
  hold (`n - r <= n` with `r == 0u64` allowed) are still refused.
- Regressions beside the `rewrite` and `instantiate` mdtests.
