# A wide viewable range carries one element's definedness across a frame

A `viewable` range bounded by a `size_t` length is the same evidence as one
bounded by an `int32`: `transport` carries it from function entry to
`defined(bytes[k])` for an index inside it. Citing the range also cites its
object-size guard, which the contract states with it.

```c filename=wide_viewable_element.c
uint64 f(uint8 bytes[], uint64 n) {
    uint64 x;
    x = 0;
    return x;
}
```

```click
verifying "wide_viewable_element.c";

uint64 f(uint8 bytes[], uint64 n) {
    requires n < 18446744073709551615u64;
    requires viewable(bytes[0..n + 1u64]);
    ensures result == 0u64 by {
        execute_until(statement(1));
        have forall (k: uint64) { k < n + 1u64 implies defined(bytes[k]) } by {
            intro();
            intro();
            transport(
                at(function.entry, viewable(bytes[0..n + 1u64])),
                defined(bytes[k])
            ) using {
                k < n + 1u64;
                at(function.entry, viewable(bytes[0..n + 1u64]));
            }
        }
        execute();
        simp();
    }
}
```

```expect
pass
```
