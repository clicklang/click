# A written cast bound types its range

A range ranges over `uint64` values when either bound is a `uint64`, and
a written cast `(uint64) n` has the type it names. So unfolding
`bytes::contains(p, 0, (uint64) n, 'x')` gives the range `(0..(uint64) n)`
a `uint64` binder, which a `uint64` witness opens. Before, a cast bound was
not recognized, the range fell back to `int32` from the literal `0`, and
the witness was refused as having the wrong type.

```c filename=a_written_cast_range_bound.c
int32 a_written_cast_range_bound(uint8 p[], int32 n) { return 0; }
```

```click
import click::bytes;

verifying "a_written_cast_range_bound.c";

int32 a_written_cast_range_bound(uint8 p[], int32 n) {
    requires viewable(p[0..n]);
    requires bytes::contains(p, 0, (uint64) n, 'x');
    ensures bytes::contains(p, 0, (uint64) n, 'x') by {
        execute();
        unfold(bytes::contains);
        obtain (found: uint64) {
            0u64 <= found and found < (uint64) n and p[found] == 'x'
        }
        witness { k: found };
        simp();
    }
}
```

```expect
pass
```
