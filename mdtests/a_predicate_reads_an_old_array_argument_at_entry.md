# a predicate reads an `old(p)` array argument at function entry

`same_first(p, old(p))` compares the first byte of `p` after the call with
the first byte before it. The C overwrites that byte with its neighbour, so
the claim does not hold in general. Unfolding the predicate binds each array
parameter to the state its argument names: `b` reads entry memory, while the
body is lowered at the current state.

```c filename=a_predicate_reads_an_old_array_argument_at_entry.c
int32 dup(uint8 p[2]) {
    p[0] = p[1];
    return 0;
}
```

```click
verifying "a_predicate_reads_an_old_array_argument_at_entry.c";

predicate same_first(a: uint8[], b: uint8[]) {
    a[0] == b[0]
}

int32 dup(uint8 p[2]) {
    consumes p[0..2];
    ensures claim: same_first(p, old(p)) by {
        step(); step();
        unfold(same_first(p, old(p)));
        normalize();
    }
}
```

```expect
fail: `normalize` goal did not normalize to true
```
