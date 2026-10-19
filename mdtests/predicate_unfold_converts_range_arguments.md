# Predicate unfolding retains parameter types

The unsuffixed literal and the narrower unsigned variable both take the
range parameter’s `uint64` type before substitution into the body.

```c filename=unfolded_literal.c
int32 unfolded_literal(uint8 p[], int32 n) { return 0; }
int32 widened_range(uint8 p[], uint32 lo, uint64 hi) { return 0; }
```

```click
import click::bytes;

verifying "unfolded_literal.c";

int32 unfolded_literal(uint8 p[], int32 n) {
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

int32 widened_range(uint8 p[], uint32 lo, uint64 hi) {
    requires viewable(p[0..hi]);
    requires bytes::contains(p, lo, hi, 'x');
    ensures bytes::contains(p, lo, hi, 'x') by {
        execute();
        unfold(bytes::contains);
        obtain (found: uint64) {
            (uint64) lo <= found and found < hi and p[found] == 'x'
        }
        witness { k: found };
        simp();
    }
}
```

```expect
pass
```
