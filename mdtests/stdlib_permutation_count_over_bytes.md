# Generic `permutation::count` counts a byte buffer

`permutation::count` is generic over the element type, so a `uint8` buffer
uses the same library fold as an `int32` array. `permutation::permutation`
stays over `int32[]`: a quantifier's type must be concrete, so a byte
permutation is a file predicate over the generic count.
`stdlib_permutation_count_over_bytes_after_a_store.md` counts a buffer after
a store.

```c filename=stdlib_permutation_count_over_bytes.c
int32 swap_bytes(uint8 p[2]) {
    uint8 tmp;
    if (p[1] < p[0]) {
        tmp = p[0];
        p[0] = p[1];
        p[1] = tmp;
    }
    return 0;
}
```

```click
import click::permutation;

verifying "stdlib_permutation_count_over_bytes.c";

predicate byte_permutation(a: uint8[], b: uint8[], lo: int32, hi: int32) {
    forall (x: uint8) {
        permutation::count(a, lo, hi, x) == permutation::count(b, lo, hi, x)
    }
}

int32 swap_bytes(uint8 p[2]) {
    consumes p[0..2];
    ensures pair_permutation: byte_permutation(p, old(p), 0, 2) by {
        unfold(byte_permutation);
    }
}
```

```expect
pass
```
