# Predicate unfolding retains the declared range type

Both supplied bounds are `uint32` variables. The predicate declares them
as `uint64`, so its unfolded range must keep that type for its witness.

```c filename=widened.c
int32 widened_range(uint8 p[], uint32 lo, uint32 hi) { return 0; }
```
```click
import click::bytes;
verifying "widened.c";
int32 widened_range(uint8 p[], uint32 lo, uint32 hi) {
    requires viewable(p[0..(uint64) hi]);
    requires bytes::contains(p, lo, hi, 'x');
    ensures bytes::contains(p, lo, hi, 'x') by {
        execute();
        unfold(bytes::contains);
        obtain (found: uint64) {
            (uint64) lo <= found and found < (uint64) hi and p[found] == 'x'
        }
        witness { k: found };
        simp();
    }
}
```

```expect
pass
```
