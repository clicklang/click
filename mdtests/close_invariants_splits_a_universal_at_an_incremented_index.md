# `close_invariants` splits a universal at an incremented index

After `p[j] = 0; j = j + 1;`, the invariant
`forall (k: int32) { 0 <= k and k < j implies p[k] == 0 }` at the back edge
covers one more cell than at iteration entry. The closer splits its body at
`k < j - 1`: below, the entry invariant holds; otherwise `k == j - 1`, the
cell just written. The second arm first needs `k <= j - 1` from
`k < j`, which is `k < j0 + 1` over the entry value `j0`. Integer arithmetic
proves it once `j0 + 1` cannot wrap, so the closer lists an available upper
bound on `j0`, here the entry invariant's `j0 <= 3`, beside `k < j`, rather
than citing a bridge lemma. `bubble_pass3_max_suffix.md` uses the same split.

```c filename=zero3.c
int32 zero3(int32 p[3]) {
    int32 j;
    j = 0;
    while (j < 3) {
        p[j] = 0;
        j = j + 1;
    }
    return 0;
}
```

```click
verifying "zero3.c";

int32 zero3(int32 p[3]) {
    consumes p[0..3];
    ensures result == 0;
} by {
    step();
    step();
    loop {
        decreases 3 - j;
        invariant j >= 0 and j <= 3;
        invariant forall (k: int32) { 0 <= k and k < j implies p[k] == 0 };
        preserve by {
            step();
            step();
            close_invariants();
        }
        owns p[0..3];
    }
    step();
}
```

```expect
pass
```
