# Generic `permutation::count` refuses a byte overwrite as a permutation

Overwriting one cell with its neighbour changes the byte counts, so the
file's byte permutation over `permutation::count` does not hold.

```c filename=stdlib_permutation_count_over_bytes_rejects_overwrite.c
int32 duplicate_byte(uint8 p[2]) {
    p[0] = p[1];
    return 0;
}
```

```click
import click::permutation;

verifying "stdlib_permutation_count_over_bytes_rejects_overwrite.c";

predicate byte_permutation(a: uint8[], b: uint8[], lo: int32, hi: int32) {
    forall (x: uint8) {
        permutation::count(a, lo, hi, x) == permutation::count(b, lo, hi, x)
    }
}

int32 duplicate_byte(uint8 p[2]) {
    consumes p[0..2];
    ensures pair_permutation: byte_permutation(p, old(p), 0, 2) by {
        unfold(byte_permutation);
    }
}
```

```expect
fail: `ensures byte_permutation(p, old(p), 0, 2)` failed for `duplicate_byte.pair_permutation`
```
