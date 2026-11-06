# Generic `permutation::count` counts a byte buffer after a store

`permutation::count` over a `uint8` buffer evaluates its fold over the
post-store cells: after `p[1] = 9` with `p[0] == 9`, the value 9 occurs
twice in `p[0..3]`.

```c filename=stdlib_permutation_count_over_bytes_after_a_store.c
int32 count_after_store(uint8 p[3]) {
    p[1] = 9;
    return 0;
}
```

```click
import click::permutation;

verifying "stdlib_permutation_count_over_bytes_after_a_store.c";

int32 count_after_store(uint8 p[3]) {
    requires p[0] == 9 and p[2] == 4;
    consumes p[0..3];
    ensures nine_twice: permutation::count(p, 0, 3, 9u8) == 2;
}
```

```expect
pass
```
