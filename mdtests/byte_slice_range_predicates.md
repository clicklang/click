# byte-slice range predicates

This checks byte-slice predicates that are useful before committing to a full
C-string abstraction. `bytes::contains` is existential for symbolic ranges, so
proof scripts can open it with `obtain (...)` after unfolding. `bytes::all_not_equal`
is universal and can be used as a finite range fact after unfolding. A byte
range is measured as C measures it, in `size_t`, so the C `int32` length `n`
is converted where it is passed: `(uint64) n`.

```c filename=byte_slice_range_predicates.c
int32 byte_slice_range_predicates(uint8 p[], int32 n) {
    return 0;
}
```

```click
import click::bytes;

verifying "byte_slice_range_predicates.c";

int32 byte_slice_range_predicates(uint8 p[], int32 n) {
    requires viewable(p[0..n]);
    requires viewable(p[0..3]);
    requires bytes::contains(p, 0u64, (uint64) n, 'x');
    requires bytes::all_not_equal(p, 0, 3, 'y');

    ensures opened_contains: bytes::contains(p, 0u64, (uint64) n, 'x') by {
        execute();
        unfold(bytes::contains);
        obtain (found: uint64) {
            0u64 <= found and found < (uint64) n and p[found] == 'x'
        }
        witness { k: found };
        simp();
    }

    ensures second_prefix_byte_is_not_y: p[1] != 'y' by {
        execute();
        unfold(bytes::all_not_equal);
        simp();
    }
}
```

```expect
pass
```
